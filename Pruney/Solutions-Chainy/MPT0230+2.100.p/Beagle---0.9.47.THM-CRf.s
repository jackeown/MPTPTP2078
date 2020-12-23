%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:08 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   77 (  94 expanded)
%              Number of leaves         :   39 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :   67 (  94 expanded)
%              Number of equality atoms :   57 (  80 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(c_78,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_80,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_66,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_64,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_68,plain,(
    ! [A_40,B_41,C_42,D_43] : k3_enumset1(A_40,A_40,B_41,C_42,D_43) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1196,plain,(
    ! [C_151,B_148,A_149,D_147,E_150] : k2_xboole_0(k2_enumset1(A_149,B_148,C_151,D_147),k1_tarski(E_150)) = k3_enumset1(A_149,B_148,C_151,D_147,E_150) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1205,plain,(
    ! [A_37,B_38,C_39,E_150] : k3_enumset1(A_37,A_37,B_38,C_39,E_150) = k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(E_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1196])).

tff(c_1259,plain,(
    ! [A_159,B_160,C_161,E_162] : k2_xboole_0(k1_enumset1(A_159,B_160,C_161),k1_tarski(E_162)) = k2_enumset1(A_159,B_160,C_161,E_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1205])).

tff(c_1298,plain,(
    ! [A_35,B_36,E_162] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(E_162)) = k2_enumset1(A_35,A_35,B_36,E_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1259])).

tff(c_1302,plain,(
    ! [A_163,B_164,E_165] : k2_xboole_0(k2_tarski(A_163,B_164),k1_tarski(E_165)) = k1_enumset1(A_163,B_164,E_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1298])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_320,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_335,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_320])).

tff(c_339,plain,(
    ! [A_98] : k4_xboole_0(A_98,k1_xboole_0) = A_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_335])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_345,plain,(
    ! [A_98] : k4_xboole_0(A_98,A_98) = k3_xboole_0(A_98,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_10])).

tff(c_353,plain,(
    ! [A_98] : k4_xboole_0(A_98,A_98) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_345])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_332,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_320])).

tff(c_484,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_332])).

tff(c_82,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_140,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = A_83
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_144,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_140])).

tff(c_329,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_320])).

tff(c_502,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_329])).

tff(c_14,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_509,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_14])).

tff(c_513,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_509])).

tff(c_1308,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1302,c_513])).

tff(c_18,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1342,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1308,c_18])).

tff(c_355,plain,(
    ! [C_99,B_100,A_101] : k1_enumset1(C_99,B_100,A_101) = k1_enumset1(A_101,B_100,C_99) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_435,plain,(
    ! [B_36,A_35] : k1_enumset1(B_36,A_35,A_35) = k2_tarski(A_35,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_355])).

tff(c_986,plain,(
    ! [E_126,C_127,B_128,A_129] :
      ( E_126 = C_127
      | E_126 = B_128
      | E_126 = A_129
      | ~ r2_hidden(E_126,k1_enumset1(A_129,B_128,C_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1001,plain,(
    ! [E_126,A_35,B_36] :
      ( E_126 = A_35
      | E_126 = A_35
      | E_126 = B_36
      | ~ r2_hidden(E_126,k2_tarski(A_35,B_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_986])).

tff(c_1363,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1342,c_1001])).

tff(c_1370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_80,c_80,c_1363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.62  
% 3.15/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.62  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 3.15/1.62  
% 3.15/1.62  %Foreground sorts:
% 3.15/1.62  
% 3.15/1.62  
% 3.15/1.62  %Background operators:
% 3.15/1.62  
% 3.15/1.62  
% 3.15/1.62  %Foreground operators:
% 3.15/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.15/1.62  tff('#skF_7', type, '#skF_7': $i).
% 3.15/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.15/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.15/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.15/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.15/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.15/1.62  
% 3.54/1.64  tff(f_95, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.54/1.64  tff(f_75, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.54/1.64  tff(f_73, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.54/1.64  tff(f_77, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.54/1.64  tff(f_69, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 3.54/1.64  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.54/1.64  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.54/1.64  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.54/1.64  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.54/1.64  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.54/1.64  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.54/1.64  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.54/1.64  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.54/1.64  tff(f_67, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 3.54/1.64  tff(c_78, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.54/1.64  tff(c_80, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.54/1.64  tff(c_66, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.54/1.64  tff(c_64, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.54/1.64  tff(c_68, plain, (![A_40, B_41, C_42, D_43]: (k3_enumset1(A_40, A_40, B_41, C_42, D_43)=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.54/1.64  tff(c_1196, plain, (![C_151, B_148, A_149, D_147, E_150]: (k2_xboole_0(k2_enumset1(A_149, B_148, C_151, D_147), k1_tarski(E_150))=k3_enumset1(A_149, B_148, C_151, D_147, E_150))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.54/1.64  tff(c_1205, plain, (![A_37, B_38, C_39, E_150]: (k3_enumset1(A_37, A_37, B_38, C_39, E_150)=k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(E_150)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1196])).
% 3.54/1.64  tff(c_1259, plain, (![A_159, B_160, C_161, E_162]: (k2_xboole_0(k1_enumset1(A_159, B_160, C_161), k1_tarski(E_162))=k2_enumset1(A_159, B_160, C_161, E_162))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1205])).
% 3.54/1.64  tff(c_1298, plain, (![A_35, B_36, E_162]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(E_162))=k2_enumset1(A_35, A_35, B_36, E_162))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1259])).
% 3.54/1.64  tff(c_1302, plain, (![A_163, B_164, E_165]: (k2_xboole_0(k2_tarski(A_163, B_164), k1_tarski(E_165))=k1_enumset1(A_163, B_164, E_165))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1298])).
% 3.54/1.64  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.64  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.64  tff(c_320, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.54/1.64  tff(c_335, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_320])).
% 3.54/1.64  tff(c_339, plain, (![A_98]: (k4_xboole_0(A_98, k1_xboole_0)=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_335])).
% 3.54/1.64  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.64  tff(c_345, plain, (![A_98]: (k4_xboole_0(A_98, A_98)=k3_xboole_0(A_98, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_339, c_10])).
% 3.54/1.64  tff(c_353, plain, (![A_98]: (k4_xboole_0(A_98, A_98)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_345])).
% 3.54/1.64  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.64  tff(c_332, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_320])).
% 3.54/1.64  tff(c_484, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_353, c_332])).
% 3.54/1.64  tff(c_82, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.54/1.64  tff(c_140, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=A_83 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.54/1.64  tff(c_144, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_82, c_140])).
% 3.54/1.64  tff(c_329, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_320])).
% 3.54/1.64  tff(c_502, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_484, c_329])).
% 3.54/1.64  tff(c_14, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.54/1.64  tff(c_509, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_502, c_14])).
% 3.54/1.64  tff(c_513, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_509])).
% 3.54/1.64  tff(c_1308, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1302, c_513])).
% 3.54/1.64  tff(c_18, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.54/1.64  tff(c_1342, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1308, c_18])).
% 3.54/1.64  tff(c_355, plain, (![C_99, B_100, A_101]: (k1_enumset1(C_99, B_100, A_101)=k1_enumset1(A_101, B_100, C_99))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.54/1.64  tff(c_435, plain, (![B_36, A_35]: (k1_enumset1(B_36, A_35, A_35)=k2_tarski(A_35, B_36))), inference(superposition, [status(thm), theory('equality')], [c_64, c_355])).
% 3.54/1.64  tff(c_986, plain, (![E_126, C_127, B_128, A_129]: (E_126=C_127 | E_126=B_128 | E_126=A_129 | ~r2_hidden(E_126, k1_enumset1(A_129, B_128, C_127)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.54/1.64  tff(c_1001, plain, (![E_126, A_35, B_36]: (E_126=A_35 | E_126=A_35 | E_126=B_36 | ~r2_hidden(E_126, k2_tarski(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_435, c_986])).
% 3.54/1.64  tff(c_1363, plain, ('#skF_5'='#skF_6' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1342, c_1001])).
% 3.54/1.64  tff(c_1370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_80, c_80, c_1363])).
% 3.54/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.64  
% 3.54/1.64  Inference rules
% 3.54/1.64  ----------------------
% 3.54/1.64  #Ref     : 0
% 3.54/1.64  #Sup     : 332
% 3.54/1.64  #Fact    : 0
% 3.54/1.64  #Define  : 0
% 3.54/1.64  #Split   : 0
% 3.54/1.64  #Chain   : 0
% 3.54/1.64  #Close   : 0
% 3.54/1.64  
% 3.54/1.64  Ordering : KBO
% 3.54/1.64  
% 3.54/1.64  Simplification rules
% 3.54/1.64  ----------------------
% 3.54/1.64  #Subsume      : 68
% 3.54/1.64  #Demod        : 139
% 3.54/1.64  #Tautology    : 201
% 3.54/1.64  #SimpNegUnit  : 1
% 3.54/1.64  #BackRed      : 0
% 3.54/1.64  
% 3.54/1.64  #Partial instantiations: 0
% 3.54/1.64  #Strategies tried      : 1
% 3.54/1.64  
% 3.54/1.64  Timing (in seconds)
% 3.54/1.64  ----------------------
% 3.54/1.64  Preprocessing        : 0.38
% 3.54/1.64  Parsing              : 0.19
% 3.54/1.64  CNF conversion       : 0.03
% 3.54/1.64  Main loop            : 0.40
% 3.54/1.64  Inferencing          : 0.13
% 3.54/1.64  Reduction            : 0.16
% 3.54/1.64  Demodulation         : 0.13
% 3.54/1.64  BG Simplification    : 0.03
% 3.54/1.64  Subsumption          : 0.07
% 3.54/1.64  Abstraction          : 0.02
% 3.54/1.64  MUC search           : 0.00
% 3.54/1.64  Cooper               : 0.00
% 3.54/1.64  Total                : 0.81
% 3.54/1.64  Index Insertion      : 0.00
% 3.54/1.64  Index Deletion       : 0.00
% 3.54/1.64  Index Matching       : 0.00
% 3.54/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
