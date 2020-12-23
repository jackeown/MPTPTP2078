%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:56 EST 2020

% Result     : Theorem 5.24s
% Output     : CNFRefutation 5.57s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 316 expanded)
%              Number of leaves         :   22 ( 116 expanded)
%              Depth                    :   16
%              Number of atoms          :   75 ( 535 expanded)
%              Number of equality atoms :   55 ( 278 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1128,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden('#skF_1'(A_96,B_97,C_98),A_96)
      | r2_hidden('#skF_2'(A_96,B_97,C_98),C_98)
      | k4_xboole_0(A_96,B_97) = C_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1214,plain,(
    ! [A_96,C_98] :
      ( r2_hidden('#skF_2'(A_96,A_96,C_98),C_98)
      | k4_xboole_0(A_96,A_96) = C_98 ) ),
    inference(resolution,[status(thm)],[c_1128,c_18])).

tff(c_1236,plain,(
    ! [A_99,C_100] :
      ( r2_hidden('#skF_2'(A_99,A_99,C_100),C_100)
      | k4_xboole_0(A_99,A_99) = C_100 ) ),
    inference(resolution,[status(thm)],[c_1128,c_18])).

tff(c_908,plain,(
    ! [A_83,C_84,B_85] :
      ( ~ r2_hidden(A_83,C_84)
      | ~ r2_hidden(A_83,B_85)
      | ~ r2_hidden(A_83,k5_xboole_0(B_85,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_920,plain,(
    ! [A_83,A_18] :
      ( ~ r2_hidden(A_83,k1_xboole_0)
      | ~ r2_hidden(A_83,A_18)
      | ~ r2_hidden(A_83,A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_908])).

tff(c_1342,plain,(
    ! [A_103,A_104] :
      ( ~ r2_hidden('#skF_2'(A_103,A_103,k1_xboole_0),A_104)
      | k4_xboole_0(A_103,A_103) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1236,c_920])).

tff(c_1366,plain,(
    ! [A_96] : k4_xboole_0(A_96,A_96) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1214,c_1342])).

tff(c_1420,plain,(
    ! [A_105] : k4_xboole_0(A_105,A_105) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1214,c_1342])).

tff(c_36,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_141,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,k4_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_123])).

tff(c_150,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_141])).

tff(c_1440,plain,(
    ! [A_105] : k4_xboole_0(A_105,A_105) = k3_xboole_0(A_105,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_150])).

tff(c_1568,plain,(
    ! [A_110] : k3_xboole_0(A_110,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1440])).

tff(c_98,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_116,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_1611,plain,(
    ! [A_110] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_1568,c_116])).

tff(c_2020,plain,(
    ! [A_121] : k4_xboole_0(k1_xboole_0,A_121) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1611])).

tff(c_42,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2076,plain,(
    ! [A_121] : k5_xboole_0(A_121,k1_xboole_0) = k2_xboole_0(A_121,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2020,c_42])).

tff(c_2107,plain,(
    ! [A_121] : k2_xboole_0(A_121,k1_xboole_0) = A_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2076])).

tff(c_147,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,k3_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_123])).

tff(c_152,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_147])).

tff(c_1464,plain,(
    ! [A_105] : k3_xboole_0(A_105,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1440])).

tff(c_221,plain,(
    ! [A_40,B_41] : k3_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_147])).

tff(c_245,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_221])).

tff(c_317,plain,(
    ! [B_53,A_54] : k3_xboole_0(B_53,k3_xboole_0(A_54,B_53)) = k3_xboole_0(B_53,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_221])).

tff(c_345,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k3_xboole_0(k3_xboole_0(A_1,B_2),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_317])).

tff(c_618,plain,(
    ! [A_79,B_80] : k3_xboole_0(k3_xboole_0(A_79,B_80),k3_xboole_0(B_80,A_79)) = k3_xboole_0(B_80,A_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_2,c_345])).

tff(c_724,plain,(
    ! [B_80,A_79] : k3_xboole_0(k3_xboole_0(B_80,A_79),k3_xboole_0(A_79,B_80)) = k3_xboole_0(B_80,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_618])).

tff(c_1582,plain,(
    ! [A_110] : k3_xboole_0(k3_xboole_0(k1_xboole_0,A_110),k1_xboole_0) = k3_xboole_0(k1_xboole_0,A_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_1568,c_724])).

tff(c_1635,plain,(
    ! [A_110] : k3_xboole_0(k1_xboole_0,A_110) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1464,c_1582])).

tff(c_721,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_618])).

tff(c_2269,plain,(
    ! [A_129] : k4_xboole_0(A_129,k1_xboole_0) = k3_xboole_0(A_129,A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_38])).

tff(c_2975,plain,(
    ! [A_149,B_150] : k4_xboole_0(k3_xboole_0(A_149,B_150),k1_xboole_0) = k3_xboole_0(B_150,A_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_2269])).

tff(c_3014,plain,(
    ! [A_149,B_150] : k4_xboole_0(k3_xboole_0(A_149,B_150),k3_xboole_0(B_150,A_149)) = k3_xboole_0(k3_xboole_0(A_149,B_150),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2975,c_38])).

tff(c_3211,plain,(
    ! [A_157,B_158] : k4_xboole_0(k3_xboole_0(A_157,B_158),k3_xboole_0(B_158,A_157)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1635,c_2,c_3014])).

tff(c_3317,plain,(
    ! [A_14,B_15] : k4_xboole_0(k3_xboole_0(A_14,B_15),k3_xboole_0(k3_xboole_0(A_14,B_15),A_14)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_3211])).

tff(c_3552,plain,(
    ! [A_164,B_165] : k4_xboole_0(k3_xboole_0(A_164,B_165),A_164) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_2,c_3317])).

tff(c_22,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),k4_xboole_0(B_10,A_9)) = k5_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3601,plain,(
    ! [A_164,B_165] : k2_xboole_0(k4_xboole_0(A_164,k3_xboole_0(A_164,B_165)),k1_xboole_0) = k5_xboole_0(A_164,k3_xboole_0(A_164,B_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3552,c_22])).

tff(c_4862,plain,(
    ! [A_186,B_187] : k5_xboole_0(A_186,k3_xboole_0(A_186,B_187)) = k4_xboole_0(A_186,B_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2107,c_36,c_3601])).

tff(c_4930,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4862])).

tff(c_44,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_45,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_4954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4930,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:33:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.24/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/2.04  
% 5.24/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/2.05  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 5.24/2.05  
% 5.24/2.05  %Foreground sorts:
% 5.24/2.05  
% 5.24/2.05  
% 5.24/2.05  %Background operators:
% 5.24/2.05  
% 5.24/2.05  
% 5.24/2.05  %Foreground operators:
% 5.24/2.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.24/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.24/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.24/2.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.24/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.24/2.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.24/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.24/2.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.24/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.24/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.24/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.24/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.24/2.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.24/2.05  
% 5.57/2.06  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.57/2.06  tff(f_52, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.57/2.06  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.57/2.06  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 5.57/2.06  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.57/2.06  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.57/2.06  tff(f_54, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.57/2.06  tff(f_39, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 5.57/2.06  tff(f_57, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.57/2.06  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.57/2.06  tff(c_40, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.57/2.06  tff(c_1128, plain, (![A_96, B_97, C_98]: (r2_hidden('#skF_1'(A_96, B_97, C_98), A_96) | r2_hidden('#skF_2'(A_96, B_97, C_98), C_98) | k4_xboole_0(A_96, B_97)=C_98)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.57/2.06  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.57/2.06  tff(c_1214, plain, (![A_96, C_98]: (r2_hidden('#skF_2'(A_96, A_96, C_98), C_98) | k4_xboole_0(A_96, A_96)=C_98)), inference(resolution, [status(thm)], [c_1128, c_18])).
% 5.57/2.06  tff(c_1236, plain, (![A_99, C_100]: (r2_hidden('#skF_2'(A_99, A_99, C_100), C_100) | k4_xboole_0(A_99, A_99)=C_100)), inference(resolution, [status(thm)], [c_1128, c_18])).
% 5.57/2.06  tff(c_908, plain, (![A_83, C_84, B_85]: (~r2_hidden(A_83, C_84) | ~r2_hidden(A_83, B_85) | ~r2_hidden(A_83, k5_xboole_0(B_85, C_84)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.57/2.06  tff(c_920, plain, (![A_83, A_18]: (~r2_hidden(A_83, k1_xboole_0) | ~r2_hidden(A_83, A_18) | ~r2_hidden(A_83, A_18))), inference(superposition, [status(thm), theory('equality')], [c_40, c_908])).
% 5.57/2.06  tff(c_1342, plain, (![A_103, A_104]: (~r2_hidden('#skF_2'(A_103, A_103, k1_xboole_0), A_104) | k4_xboole_0(A_103, A_103)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1236, c_920])).
% 5.57/2.06  tff(c_1366, plain, (![A_96]: (k4_xboole_0(A_96, A_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1214, c_1342])).
% 5.57/2.06  tff(c_1420, plain, (![A_105]: (k4_xboole_0(A_105, A_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1214, c_1342])).
% 5.57/2.06  tff(c_36, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.57/2.06  tff(c_38, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.57/2.06  tff(c_123, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.57/2.06  tff(c_141, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k3_xboole_0(A_16, k4_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_123])).
% 5.57/2.06  tff(c_150, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_141])).
% 5.57/2.06  tff(c_1440, plain, (![A_105]: (k4_xboole_0(A_105, A_105)=k3_xboole_0(A_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_150])).
% 5.57/2.06  tff(c_1568, plain, (![A_110]: (k3_xboole_0(A_110, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_1440])).
% 5.57/2.06  tff(c_98, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.57/2.06  tff(c_116, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_98])).
% 5.57/2.06  tff(c_1611, plain, (![A_110]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_110))), inference(superposition, [status(thm), theory('equality')], [c_1568, c_116])).
% 5.57/2.06  tff(c_2020, plain, (![A_121]: (k4_xboole_0(k1_xboole_0, A_121)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_1611])).
% 5.57/2.06  tff(c_42, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.57/2.06  tff(c_2076, plain, (![A_121]: (k5_xboole_0(A_121, k1_xboole_0)=k2_xboole_0(A_121, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2020, c_42])).
% 5.57/2.06  tff(c_2107, plain, (![A_121]: (k2_xboole_0(A_121, k1_xboole_0)=A_121)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2076])).
% 5.57/2.06  tff(c_147, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, k3_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_123])).
% 5.57/2.06  tff(c_152, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_147])).
% 5.57/2.06  tff(c_1464, plain, (![A_105]: (k3_xboole_0(A_105, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_1440])).
% 5.57/2.06  tff(c_221, plain, (![A_40, B_41]: (k3_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_147])).
% 5.57/2.06  tff(c_245, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_221])).
% 5.57/2.06  tff(c_317, plain, (![B_53, A_54]: (k3_xboole_0(B_53, k3_xboole_0(A_54, B_53))=k3_xboole_0(B_53, A_54))), inference(superposition, [status(thm), theory('equality')], [c_2, c_221])).
% 5.57/2.06  tff(c_345, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k3_xboole_0(k3_xboole_0(A_1, B_2), B_2))), inference(superposition, [status(thm), theory('equality')], [c_245, c_317])).
% 5.57/2.06  tff(c_618, plain, (![A_79, B_80]: (k3_xboole_0(k3_xboole_0(A_79, B_80), k3_xboole_0(B_80, A_79))=k3_xboole_0(B_80, A_79))), inference(demodulation, [status(thm), theory('equality')], [c_245, c_2, c_345])).
% 5.57/2.06  tff(c_724, plain, (![B_80, A_79]: (k3_xboole_0(k3_xboole_0(B_80, A_79), k3_xboole_0(A_79, B_80))=k3_xboole_0(B_80, A_79))), inference(superposition, [status(thm), theory('equality')], [c_2, c_618])).
% 5.57/2.06  tff(c_1582, plain, (![A_110]: (k3_xboole_0(k3_xboole_0(k1_xboole_0, A_110), k1_xboole_0)=k3_xboole_0(k1_xboole_0, A_110))), inference(superposition, [status(thm), theory('equality')], [c_1568, c_724])).
% 5.57/2.06  tff(c_1635, plain, (![A_110]: (k3_xboole_0(k1_xboole_0, A_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1464, c_1582])).
% 5.57/2.06  tff(c_721, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_618])).
% 5.57/2.06  tff(c_2269, plain, (![A_129]: (k4_xboole_0(A_129, k1_xboole_0)=k3_xboole_0(A_129, A_129))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_38])).
% 5.57/2.06  tff(c_2975, plain, (![A_149, B_150]: (k4_xboole_0(k3_xboole_0(A_149, B_150), k1_xboole_0)=k3_xboole_0(B_150, A_149))), inference(superposition, [status(thm), theory('equality')], [c_721, c_2269])).
% 5.57/2.06  tff(c_3014, plain, (![A_149, B_150]: (k4_xboole_0(k3_xboole_0(A_149, B_150), k3_xboole_0(B_150, A_149))=k3_xboole_0(k3_xboole_0(A_149, B_150), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2975, c_38])).
% 5.57/2.06  tff(c_3211, plain, (![A_157, B_158]: (k4_xboole_0(k3_xboole_0(A_157, B_158), k3_xboole_0(B_158, A_157))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1635, c_2, c_3014])).
% 5.57/2.06  tff(c_3317, plain, (![A_14, B_15]: (k4_xboole_0(k3_xboole_0(A_14, B_15), k3_xboole_0(k3_xboole_0(A_14, B_15), A_14))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_3211])).
% 5.57/2.06  tff(c_3552, plain, (![A_164, B_165]: (k4_xboole_0(k3_xboole_0(A_164, B_165), A_164)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_2, c_3317])).
% 5.57/2.06  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), k4_xboole_0(B_10, A_9))=k5_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.57/2.06  tff(c_3601, plain, (![A_164, B_165]: (k2_xboole_0(k4_xboole_0(A_164, k3_xboole_0(A_164, B_165)), k1_xboole_0)=k5_xboole_0(A_164, k3_xboole_0(A_164, B_165)))), inference(superposition, [status(thm), theory('equality')], [c_3552, c_22])).
% 5.57/2.06  tff(c_4862, plain, (![A_186, B_187]: (k5_xboole_0(A_186, k3_xboole_0(A_186, B_187))=k4_xboole_0(A_186, B_187))), inference(demodulation, [status(thm), theory('equality')], [c_2107, c_36, c_3601])).
% 5.57/2.06  tff(c_4930, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4862])).
% 5.57/2.06  tff(c_44, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.57/2.06  tff(c_45, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 5.57/2.06  tff(c_4954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4930, c_45])).
% 5.57/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.57/2.06  
% 5.57/2.06  Inference rules
% 5.57/2.06  ----------------------
% 5.57/2.06  #Ref     : 0
% 5.57/2.06  #Sup     : 1218
% 5.57/2.06  #Fact    : 0
% 5.57/2.06  #Define  : 0
% 5.57/2.06  #Split   : 0
% 5.57/2.06  #Chain   : 0
% 5.57/2.06  #Close   : 0
% 5.57/2.06  
% 5.57/2.06  Ordering : KBO
% 5.57/2.06  
% 5.57/2.06  Simplification rules
% 5.57/2.06  ----------------------
% 5.57/2.06  #Subsume      : 205
% 5.57/2.06  #Demod        : 1344
% 5.57/2.06  #Tautology    : 733
% 5.57/2.06  #SimpNegUnit  : 0
% 5.57/2.06  #BackRed      : 3
% 5.57/2.06  
% 5.57/2.06  #Partial instantiations: 0
% 5.57/2.06  #Strategies tried      : 1
% 5.57/2.06  
% 5.57/2.06  Timing (in seconds)
% 5.57/2.06  ----------------------
% 5.57/2.06  Preprocessing        : 0.29
% 5.57/2.06  Parsing              : 0.15
% 5.57/2.06  CNF conversion       : 0.02
% 5.57/2.07  Main loop            : 1.00
% 5.57/2.07  Inferencing          : 0.28
% 5.57/2.07  Reduction            : 0.44
% 5.57/2.07  Demodulation         : 0.37
% 5.57/2.07  BG Simplification    : 0.03
% 5.57/2.07  Subsumption          : 0.19
% 5.57/2.07  Abstraction          : 0.05
% 5.57/2.07  MUC search           : 0.00
% 5.57/2.07  Cooper               : 0.00
% 5.57/2.07  Total                : 1.32
% 5.57/2.07  Index Insertion      : 0.00
% 5.57/2.07  Index Deletion       : 0.00
% 5.57/2.07  Index Matching       : 0.00
% 5.57/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
