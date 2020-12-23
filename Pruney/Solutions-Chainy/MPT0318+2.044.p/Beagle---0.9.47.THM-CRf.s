%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:07 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 143 expanded)
%              Number of leaves         :   29 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 202 expanded)
%              Number of equality atoms :   64 ( 200 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_28,plain,(
    ! [B_27] : k2_zfmisc_1(k1_xboole_0,B_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_247,plain,(
    ! [A_52,B_53,C_54] : k5_xboole_0(k5_xboole_0(A_52,B_53),C_54) = k5_xboole_0(A_52,k5_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_717,plain,(
    ! [A_64,C_65] : k5_xboole_0(A_64,k5_xboole_0(A_64,C_65)) = k5_xboole_0(k1_xboole_0,C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_247])).

tff(c_822,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,A_7) = k5_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_717])).

tff(c_852,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_822])).

tff(c_401,plain,(
    ! [A_58,B_59] : k5_xboole_0(k5_xboole_0(A_58,B_59),k2_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_447,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_7,A_7)) = k3_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_401])).

tff(c_864,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k2_xboole_0(A_7,A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_447])).

tff(c_871,plain,(
    ! [A_70] : k5_xboole_0(k1_xboole_0,A_70) = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_822])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_895,plain,(
    ! [B_2] : k4_xboole_0(k1_xboole_0,B_2) = k3_xboole_0(k1_xboole_0,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_2])).

tff(c_34,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_116,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_147,plain,(
    ! [B_43,A_44] :
      ( k1_xboole_0 = B_43
      | k1_xboole_0 = A_44
      | k2_zfmisc_1(A_44,B_43) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_150,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_147])).

tff(c_159,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_150])).

tff(c_30,plain,(
    ! [B_29] : k4_xboole_0(k1_tarski(B_29),k1_tarski(B_29)) != k1_tarski(B_29) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_172,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) != k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_30])).

tff(c_178,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_159,c_172])).

tff(c_1055,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_178])).

tff(c_1056,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_1055])).

tff(c_14,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1146,plain,(
    ! [A_77,B_78,C_79,D_80] : k2_xboole_0(k1_tarski(A_77),k1_enumset1(B_78,C_79,D_80)) = k2_enumset1(A_77,B_78,C_79,D_80) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1337,plain,(
    ! [B_85,C_86,D_87] : k2_xboole_0(k1_xboole_0,k1_enumset1(B_85,C_86,D_87)) = k2_enumset1('#skF_2',B_85,C_86,D_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_1146])).

tff(c_1617,plain,(
    ! [A_92,B_93] : k2_xboole_0(k1_xboole_0,k2_tarski(A_92,B_93)) = k2_enumset1('#skF_2',A_92,A_92,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1337])).

tff(c_1815,plain,(
    ! [A_94] : k2_xboole_0(k1_xboole_0,k1_tarski(A_94)) = k2_enumset1('#skF_2',A_94,A_94,A_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1617])).

tff(c_1840,plain,(
    k2_enumset1('#skF_2','#skF_2','#skF_2','#skF_2') = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_1815])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] : k2_enumset1(A_17,A_17,B_18,C_19) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2060,plain,(
    k1_enumset1('#skF_2','#skF_2','#skF_2') = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1840,c_18])).

tff(c_2066,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_14,c_16,c_2060])).

tff(c_2068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1056,c_2066])).

tff(c_2069,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2101,plain,(
    ! [B_102,A_103] :
      ( k1_xboole_0 = B_102
      | k1_xboole_0 = A_103
      | k2_zfmisc_1(A_103,B_102) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2104,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2069,c_2101])).

tff(c_2113,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2104])).

tff(c_2070,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2127,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2113,c_2070])).

tff(c_2131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.64  
% 3.66/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.65  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.66/1.65  
% 3.66/1.65  %Foreground sorts:
% 3.66/1.65  
% 3.66/1.65  
% 3.66/1.65  %Background operators:
% 3.66/1.65  
% 3.66/1.65  
% 3.66/1.65  %Foreground operators:
% 3.66/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.66/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.66/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.66/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.66/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.66/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.66/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.66/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.66/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.66/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.65  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.66/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.66/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.66/1.65  
% 3.66/1.66  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.66/1.66  tff(f_68, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 3.66/1.66  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.66/1.66  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.66/1.66  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.66/1.66  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.66/1.66  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.66/1.66  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.66/1.66  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.66/1.66  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.66/1.66  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.66/1.66  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.66/1.66  tff(c_28, plain, (![B_27]: (k2_zfmisc_1(k1_xboole_0, B_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.66/1.66  tff(c_36, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.66/1.66  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.66/1.66  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.66/1.66  tff(c_247, plain, (![A_52, B_53, C_54]: (k5_xboole_0(k5_xboole_0(A_52, B_53), C_54)=k5_xboole_0(A_52, k5_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.66/1.66  tff(c_717, plain, (![A_64, C_65]: (k5_xboole_0(A_64, k5_xboole_0(A_64, C_65))=k5_xboole_0(k1_xboole_0, C_65))), inference(superposition, [status(thm), theory('equality')], [c_8, c_247])).
% 3.66/1.66  tff(c_822, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, A_7)=k5_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_717])).
% 3.66/1.66  tff(c_852, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_822])).
% 3.66/1.66  tff(c_401, plain, (![A_58, B_59]: (k5_xboole_0(k5_xboole_0(A_58, B_59), k2_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.66/1.66  tff(c_447, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_7, A_7))=k3_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_401])).
% 3.66/1.66  tff(c_864, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k2_xboole_0(A_7, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_852, c_447])).
% 3.66/1.66  tff(c_871, plain, (![A_70]: (k5_xboole_0(k1_xboole_0, A_70)=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_822])).
% 3.66/1.66  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.66/1.66  tff(c_895, plain, (![B_2]: (k4_xboole_0(k1_xboole_0, B_2)=k3_xboole_0(k1_xboole_0, B_2))), inference(superposition, [status(thm), theory('equality')], [c_871, c_2])).
% 3.66/1.66  tff(c_34, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.66/1.66  tff(c_116, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 3.66/1.66  tff(c_147, plain, (![B_43, A_44]: (k1_xboole_0=B_43 | k1_xboole_0=A_44 | k2_zfmisc_1(A_44, B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.66/1.66  tff(c_150, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_116, c_147])).
% 3.66/1.66  tff(c_159, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_36, c_150])).
% 3.66/1.66  tff(c_30, plain, (![B_29]: (k4_xboole_0(k1_tarski(B_29), k1_tarski(B_29))!=k1_tarski(B_29))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.66/1.66  tff(c_172, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))!=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_159, c_30])).
% 3.66/1.66  tff(c_178, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_159, c_159, c_172])).
% 3.66/1.66  tff(c_1055, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_895, c_178])).
% 3.66/1.66  tff(c_1056, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_864, c_1055])).
% 3.66/1.66  tff(c_14, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.66/1.66  tff(c_16, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.66/1.66  tff(c_1146, plain, (![A_77, B_78, C_79, D_80]: (k2_xboole_0(k1_tarski(A_77), k1_enumset1(B_78, C_79, D_80))=k2_enumset1(A_77, B_78, C_79, D_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.66/1.66  tff(c_1337, plain, (![B_85, C_86, D_87]: (k2_xboole_0(k1_xboole_0, k1_enumset1(B_85, C_86, D_87))=k2_enumset1('#skF_2', B_85, C_86, D_87))), inference(superposition, [status(thm), theory('equality')], [c_159, c_1146])).
% 3.66/1.66  tff(c_1617, plain, (![A_92, B_93]: (k2_xboole_0(k1_xboole_0, k2_tarski(A_92, B_93))=k2_enumset1('#skF_2', A_92, A_92, B_93))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1337])).
% 3.66/1.66  tff(c_1815, plain, (![A_94]: (k2_xboole_0(k1_xboole_0, k1_tarski(A_94))=k2_enumset1('#skF_2', A_94, A_94, A_94))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1617])).
% 3.66/1.66  tff(c_1840, plain, (k2_enumset1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_159, c_1815])).
% 3.66/1.66  tff(c_18, plain, (![A_17, B_18, C_19]: (k2_enumset1(A_17, A_17, B_18, C_19)=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.66/1.66  tff(c_2060, plain, (k1_enumset1('#skF_2', '#skF_2', '#skF_2')=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1840, c_18])).
% 3.66/1.66  tff(c_2066, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_159, c_14, c_16, c_2060])).
% 3.66/1.66  tff(c_2068, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1056, c_2066])).
% 3.66/1.66  tff(c_2069, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.66/1.66  tff(c_2101, plain, (![B_102, A_103]: (k1_xboole_0=B_102 | k1_xboole_0=A_103 | k2_zfmisc_1(A_103, B_102)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.66/1.66  tff(c_2104, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2069, c_2101])).
% 3.66/1.66  tff(c_2113, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_36, c_2104])).
% 3.66/1.66  tff(c_2070, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.66/1.66  tff(c_2127, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2113, c_2070])).
% 3.66/1.66  tff(c_2131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_2127])).
% 3.66/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.66  
% 3.66/1.66  Inference rules
% 3.66/1.66  ----------------------
% 3.66/1.66  #Ref     : 0
% 3.66/1.66  #Sup     : 527
% 3.66/1.66  #Fact    : 0
% 3.66/1.66  #Define  : 0
% 3.66/1.66  #Split   : 1
% 3.66/1.66  #Chain   : 0
% 3.66/1.66  #Close   : 0
% 3.66/1.66  
% 3.66/1.66  Ordering : KBO
% 3.66/1.66  
% 3.66/1.66  Simplification rules
% 3.66/1.66  ----------------------
% 3.66/1.66  #Subsume      : 10
% 3.66/1.66  #Demod        : 332
% 3.66/1.66  #Tautology    : 348
% 3.66/1.66  #SimpNegUnit  : 6
% 3.66/1.66  #BackRed      : 13
% 3.66/1.66  
% 3.66/1.66  #Partial instantiations: 0
% 3.66/1.66  #Strategies tried      : 1
% 3.66/1.66  
% 3.66/1.66  Timing (in seconds)
% 3.66/1.66  ----------------------
% 3.66/1.66  Preprocessing        : 0.33
% 3.66/1.66  Parsing              : 0.18
% 3.66/1.66  CNF conversion       : 0.02
% 3.66/1.66  Main loop            : 0.53
% 3.66/1.66  Inferencing          : 0.18
% 3.66/1.66  Reduction            : 0.21
% 3.66/1.66  Demodulation         : 0.16
% 3.66/1.66  BG Simplification    : 0.03
% 3.66/1.66  Subsumption          : 0.08
% 3.66/1.66  Abstraction          : 0.03
% 3.66/1.66  MUC search           : 0.00
% 3.66/1.66  Cooper               : 0.00
% 3.66/1.66  Total                : 0.90
% 3.66/1.66  Index Insertion      : 0.00
% 3.66/1.66  Index Deletion       : 0.00
% 3.66/1.66  Index Matching       : 0.00
% 3.66/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
