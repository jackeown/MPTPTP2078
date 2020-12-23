%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:15 EST 2020

% Result     : Theorem 6.43s
% Output     : CNFRefutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 127 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :   81 ( 142 expanded)
%              Number of equality atoms :   48 (  98 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_42,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_224,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_240,plain,(
    ! [B_47,A_48] : k3_tarski(k2_tarski(B_47,A_48)) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_224])).

tff(c_30,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_264,plain,(
    ! [B_49,A_50] : k2_xboole_0(B_49,A_50) = k2_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_30])).

tff(c_280,plain,(
    ! [A_50] : k2_xboole_0(k1_xboole_0,A_50) = A_50 ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_12])).

tff(c_420,plain,(
    ! [A_62,B_63] : k2_xboole_0(A_62,k4_xboole_0(B_63,A_62)) = k2_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_430,plain,(
    ! [B_63] : k4_xboole_0(B_63,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_280])).

tff(c_448,plain,(
    ! [B_63] : k4_xboole_0(B_63,k1_xboole_0) = B_63 ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_430])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_130,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [A_42] : k3_xboole_0(k1_xboole_0,A_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_130])).

tff(c_157,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_139])).

tff(c_571,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_580,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k4_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_571])).

tff(c_595,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_580])).

tff(c_137,plain,(
    ! [A_10] : k3_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_130])).

tff(c_586,plain,(
    ! [A_10] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_571])).

tff(c_606,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_586])).

tff(c_380,plain,(
    ! [A_59,B_60] : k4_xboole_0(k2_xboole_0(A_59,B_60),B_60) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_389,plain,(
    ! [A_50] : k4_xboole_0(k1_xboole_0,A_50) = k4_xboole_0(A_50,A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_380])).

tff(c_607,plain,(
    ! [A_50] : k4_xboole_0(A_50,A_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_389])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_138,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_130])).

tff(c_583,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_571])).

tff(c_665,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_583])).

tff(c_1052,plain,(
    ! [A_98,B_99,C_100] :
      ( r1_tarski(k2_tarski(A_98,B_99),C_100)
      | ~ r2_hidden(B_99,C_100)
      | ~ r2_hidden(A_98,C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1949,plain,(
    ! [A_117,B_118,C_119] :
      ( k3_xboole_0(k2_tarski(A_117,B_118),C_119) = k2_tarski(A_117,B_118)
      | ~ r2_hidden(B_118,C_119)
      | ~ r2_hidden(A_117,C_119) ) ),
    inference(resolution,[status(thm)],[c_1052,c_14])).

tff(c_4692,plain,(
    ! [A_152,A_153,B_154] :
      ( k3_xboole_0(A_152,k2_tarski(A_153,B_154)) = k2_tarski(A_153,B_154)
      | ~ r2_hidden(B_154,A_152)
      | ~ r2_hidden(A_153,A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1949])).

tff(c_592,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_571])).

tff(c_4706,plain,(
    ! [A_153,B_154,A_152] :
      ( k5_xboole_0(k2_tarski(A_153,B_154),k2_tarski(A_153,B_154)) = k4_xboole_0(k2_tarski(A_153,B_154),A_152)
      | ~ r2_hidden(B_154,A_152)
      | ~ r2_hidden(A_153,A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4692,c_592])).

tff(c_7256,plain,(
    ! [A_184,B_185,A_186] :
      ( k4_xboole_0(k2_tarski(A_184,B_185),A_186) = k1_xboole_0
      | ~ r2_hidden(B_185,A_186)
      | ~ r2_hidden(A_184,A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_4706])).

tff(c_18,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7359,plain,(
    ! [A_186,A_184,B_185] :
      ( k2_xboole_0(A_186,k2_tarski(A_184,B_185)) = k2_xboole_0(A_186,k1_xboole_0)
      | ~ r2_hidden(B_185,A_186)
      | ~ r2_hidden(A_184,A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7256,c_18])).

tff(c_9071,plain,(
    ! [A_207,A_208,B_209] :
      ( k2_xboole_0(A_207,k2_tarski(A_208,B_209)) = A_207
      | ~ r2_hidden(B_209,A_207)
      | ~ r2_hidden(A_208,A_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_7359])).

tff(c_246,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_30])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_263,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_38])).

tff(c_9234,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9071,c_263])).

tff(c_9335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_9234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.43/2.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.43/2.61  
% 6.43/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.43/2.61  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.43/2.61  
% 6.43/2.61  %Foreground sorts:
% 6.43/2.61  
% 6.43/2.61  
% 6.43/2.61  %Background operators:
% 6.43/2.61  
% 6.43/2.61  
% 6.43/2.61  %Foreground operators:
% 6.43/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.43/2.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.43/2.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.43/2.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.43/2.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.43/2.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.43/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.43/2.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.43/2.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.43/2.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.43/2.61  tff('#skF_2', type, '#skF_2': $i).
% 6.43/2.61  tff('#skF_3', type, '#skF_3': $i).
% 6.43/2.61  tff('#skF_1', type, '#skF_1': $i).
% 6.43/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.43/2.61  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.43/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.43/2.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.43/2.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.43/2.61  
% 6.43/2.63  tff(f_70, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 6.43/2.63  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.43/2.63  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.43/2.63  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.43/2.63  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.43/2.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.43/2.63  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.43/2.63  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.43/2.63  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.43/2.63  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.43/2.63  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.43/2.63  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.43/2.63  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.43/2.63  tff(c_40, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.43/2.63  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.43/2.63  tff(c_22, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.43/2.63  tff(c_224, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.43/2.63  tff(c_240, plain, (![B_47, A_48]: (k3_tarski(k2_tarski(B_47, A_48))=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_22, c_224])).
% 6.43/2.63  tff(c_30, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.43/2.63  tff(c_264, plain, (![B_49, A_50]: (k2_xboole_0(B_49, A_50)=k2_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_240, c_30])).
% 6.43/2.63  tff(c_280, plain, (![A_50]: (k2_xboole_0(k1_xboole_0, A_50)=A_50)), inference(superposition, [status(thm), theory('equality')], [c_264, c_12])).
% 6.43/2.63  tff(c_420, plain, (![A_62, B_63]: (k2_xboole_0(A_62, k4_xboole_0(B_63, A_62))=k2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.43/2.63  tff(c_430, plain, (![B_63]: (k4_xboole_0(B_63, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_63))), inference(superposition, [status(thm), theory('equality')], [c_420, c_280])).
% 6.43/2.63  tff(c_448, plain, (![B_63]: (k4_xboole_0(B_63, k1_xboole_0)=B_63)), inference(demodulation, [status(thm), theory('equality')], [c_280, c_430])).
% 6.43/2.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.43/2.63  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.43/2.63  tff(c_130, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.43/2.63  tff(c_139, plain, (![A_42]: (k3_xboole_0(k1_xboole_0, A_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_130])).
% 6.43/2.63  tff(c_157, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_139])).
% 6.43/2.63  tff(c_571, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.43/2.63  tff(c_580, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k4_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_157, c_571])).
% 6.43/2.63  tff(c_595, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_448, c_580])).
% 6.43/2.63  tff(c_137, plain, (![A_10]: (k3_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_130])).
% 6.43/2.63  tff(c_586, plain, (![A_10]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_10))), inference(superposition, [status(thm), theory('equality')], [c_137, c_571])).
% 6.43/2.63  tff(c_606, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_595, c_586])).
% 6.43/2.63  tff(c_380, plain, (![A_59, B_60]: (k4_xboole_0(k2_xboole_0(A_59, B_60), B_60)=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.43/2.63  tff(c_389, plain, (![A_50]: (k4_xboole_0(k1_xboole_0, A_50)=k4_xboole_0(A_50, A_50))), inference(superposition, [status(thm), theory('equality')], [c_280, c_380])).
% 6.43/2.63  tff(c_607, plain, (![A_50]: (k4_xboole_0(A_50, A_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_606, c_389])).
% 6.43/2.63  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.43/2.63  tff(c_138, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_130])).
% 6.43/2.63  tff(c_583, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_138, c_571])).
% 6.43/2.63  tff(c_665, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_607, c_583])).
% 6.43/2.63  tff(c_1052, plain, (![A_98, B_99, C_100]: (r1_tarski(k2_tarski(A_98, B_99), C_100) | ~r2_hidden(B_99, C_100) | ~r2_hidden(A_98, C_100))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.43/2.63  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.43/2.63  tff(c_1949, plain, (![A_117, B_118, C_119]: (k3_xboole_0(k2_tarski(A_117, B_118), C_119)=k2_tarski(A_117, B_118) | ~r2_hidden(B_118, C_119) | ~r2_hidden(A_117, C_119))), inference(resolution, [status(thm)], [c_1052, c_14])).
% 6.43/2.63  tff(c_4692, plain, (![A_152, A_153, B_154]: (k3_xboole_0(A_152, k2_tarski(A_153, B_154))=k2_tarski(A_153, B_154) | ~r2_hidden(B_154, A_152) | ~r2_hidden(A_153, A_152))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1949])).
% 6.43/2.63  tff(c_592, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_571])).
% 6.43/2.63  tff(c_4706, plain, (![A_153, B_154, A_152]: (k5_xboole_0(k2_tarski(A_153, B_154), k2_tarski(A_153, B_154))=k4_xboole_0(k2_tarski(A_153, B_154), A_152) | ~r2_hidden(B_154, A_152) | ~r2_hidden(A_153, A_152))), inference(superposition, [status(thm), theory('equality')], [c_4692, c_592])).
% 6.43/2.63  tff(c_7256, plain, (![A_184, B_185, A_186]: (k4_xboole_0(k2_tarski(A_184, B_185), A_186)=k1_xboole_0 | ~r2_hidden(B_185, A_186) | ~r2_hidden(A_184, A_186))), inference(demodulation, [status(thm), theory('equality')], [c_665, c_4706])).
% 6.43/2.63  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.43/2.63  tff(c_7359, plain, (![A_186, A_184, B_185]: (k2_xboole_0(A_186, k2_tarski(A_184, B_185))=k2_xboole_0(A_186, k1_xboole_0) | ~r2_hidden(B_185, A_186) | ~r2_hidden(A_184, A_186))), inference(superposition, [status(thm), theory('equality')], [c_7256, c_18])).
% 6.43/2.63  tff(c_9071, plain, (![A_207, A_208, B_209]: (k2_xboole_0(A_207, k2_tarski(A_208, B_209))=A_207 | ~r2_hidden(B_209, A_207) | ~r2_hidden(A_208, A_207))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_7359])).
% 6.43/2.63  tff(c_246, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_240, c_30])).
% 6.43/2.63  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.43/2.63  tff(c_263, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_38])).
% 6.43/2.63  tff(c_9234, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9071, c_263])).
% 6.43/2.63  tff(c_9335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_9234])).
% 6.43/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.43/2.63  
% 6.43/2.63  Inference rules
% 6.43/2.63  ----------------------
% 6.43/2.63  #Ref     : 0
% 6.43/2.63  #Sup     : 2278
% 6.43/2.63  #Fact    : 0
% 6.43/2.63  #Define  : 0
% 6.43/2.63  #Split   : 0
% 6.43/2.63  #Chain   : 0
% 6.43/2.63  #Close   : 0
% 6.43/2.63  
% 6.43/2.63  Ordering : KBO
% 6.43/2.63  
% 6.43/2.63  Simplification rules
% 6.43/2.63  ----------------------
% 6.43/2.63  #Subsume      : 259
% 6.43/2.63  #Demod        : 4988
% 6.43/2.63  #Tautology    : 1698
% 6.43/2.63  #SimpNegUnit  : 0
% 6.43/2.63  #BackRed      : 3
% 6.43/2.63  
% 6.43/2.63  #Partial instantiations: 0
% 6.43/2.63  #Strategies tried      : 1
% 6.43/2.63  
% 6.43/2.63  Timing (in seconds)
% 6.43/2.63  ----------------------
% 6.43/2.63  Preprocessing        : 0.30
% 6.43/2.63  Parsing              : 0.16
% 6.43/2.63  CNF conversion       : 0.02
% 6.43/2.63  Main loop            : 1.57
% 6.43/2.63  Inferencing          : 0.37
% 6.43/2.63  Reduction            : 0.96
% 6.43/2.63  Demodulation         : 0.87
% 6.43/2.63  BG Simplification    : 0.03
% 6.43/2.63  Subsumption          : 0.15
% 6.43/2.63  Abstraction          : 0.09
% 6.43/2.63  MUC search           : 0.00
% 6.43/2.63  Cooper               : 0.00
% 6.43/2.63  Total                : 1.90
% 6.43/2.63  Index Insertion      : 0.00
% 6.43/2.63  Index Deletion       : 0.00
% 6.43/2.63  Index Matching       : 0.00
% 6.43/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
