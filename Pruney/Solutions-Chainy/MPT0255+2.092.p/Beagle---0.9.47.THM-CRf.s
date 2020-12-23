%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:51 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 264 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :   14
%              Number of atoms          :   62 ( 260 expanded)
%              Number of equality atoms :   53 ( 206 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_75,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_48,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_271,plain,(
    ! [A_70,B_71] : k3_xboole_0(A_70,k2_xboole_0(A_70,B_71)) = A_70 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_291,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k2_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_271])).

tff(c_297,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_291])).

tff(c_425,plain,(
    ! [A_79,B_80] : k3_tarski(k2_tarski(A_79,B_80)) = k2_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_434,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_425])).

tff(c_440,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_434])).

tff(c_12,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_313,plain,(
    ! [B_72,A_73] : k3_xboole_0(B_72,A_73) = k3_xboole_0(A_73,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_388,plain,(
    ! [B_74,A_75] : r1_tarski(k3_xboole_0(B_74,A_75),A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_10])).

tff(c_401,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_388])).

tff(c_444,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_401])).

tff(c_16,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_454,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_444,c_16])).

tff(c_24,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_463,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_24])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_608,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_637,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_608])).

tff(c_644,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_637])).

tff(c_44,plain,(
    ! [B_55] : k4_xboole_0(k1_tarski(B_55),k1_tarski(B_55)) != k1_tarski(B_55) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_747,plain,(
    ! [B_55] : k1_tarski(B_55) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_44])).

tff(c_20,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_465,plain,(
    ! [A_17] : k5_xboole_0(A_17,'#skF_1') = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_20])).

tff(c_117,plain,(
    ! [A_62,B_63] : r1_tarski(k3_xboole_0(A_62,B_63),A_62) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_128,plain,(
    ! [B_63] : k3_xboole_0(k1_xboole_0,B_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117,c_16])).

tff(c_460,plain,(
    ! [B_63] : k3_xboole_0('#skF_1',B_63) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_454,c_128])).

tff(c_176,plain,(
    ! [B_67,A_68] : k5_xboole_0(B_67,A_68) = k5_xboole_0(A_68,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_192,plain,(
    ! [A_68] : k5_xboole_0(k1_xboole_0,A_68) = A_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_20])).

tff(c_459,plain,(
    ! [A_68] : k5_xboole_0('#skF_1',A_68) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_192])).

tff(c_882,plain,(
    ! [A_102,B_103] : k5_xboole_0(k5_xboole_0(A_102,B_103),k3_xboole_0(A_102,B_103)) = k2_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_912,plain,(
    ! [A_68] : k5_xboole_0(A_68,k3_xboole_0('#skF_1',A_68)) = k2_xboole_0('#skF_1',A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_882])).

tff(c_999,plain,(
    ! [A_106] : k2_xboole_0('#skF_1',A_106) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_460,c_912])).

tff(c_456,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_440])).

tff(c_1013,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_456])).

tff(c_458,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_297])).

tff(c_1139,plain,(
    k2_tarski('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1013,c_458])).

tff(c_28,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1162,plain,(
    k1_tarski('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1139,c_28])).

tff(c_1170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_747,c_1162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:42:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.42  
% 2.64/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.43  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.64/1.43  
% 2.64/1.43  %Foreground sorts:
% 2.64/1.43  
% 2.64/1.43  
% 2.64/1.43  %Background operators:
% 2.64/1.43  
% 2.64/1.43  
% 2.64/1.43  %Foreground operators:
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.64/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.64/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.64/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.64/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.64/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.64/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.64/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.64/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.64/1.43  
% 2.64/1.44  tff(f_75, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.64/1.44  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.64/1.44  tff(f_79, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.64/1.44  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.64/1.44  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.64/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.64/1.44  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.64/1.44  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.64/1.44  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.64/1.44  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.64/1.44  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.64/1.44  tff(f_74, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.64/1.44  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.64/1.44  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.64/1.44  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 2.64/1.44  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.64/1.44  tff(c_48, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.64/1.44  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.64/1.44  tff(c_50, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.64/1.44  tff(c_271, plain, (![A_70, B_71]: (k3_xboole_0(A_70, k2_xboole_0(A_70, B_71))=A_70)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.64/1.44  tff(c_291, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k2_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_50, c_271])).
% 2.64/1.44  tff(c_297, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_291])).
% 2.64/1.44  tff(c_425, plain, (![A_79, B_80]: (k3_tarski(k2_tarski(A_79, B_80))=k2_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.64/1.44  tff(c_434, plain, (k2_xboole_0('#skF_1', '#skF_2')=k3_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_297, c_425])).
% 2.64/1.44  tff(c_440, plain, (k2_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_434])).
% 2.64/1.44  tff(c_12, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.64/1.44  tff(c_313, plain, (![B_72, A_73]: (k3_xboole_0(B_72, A_73)=k3_xboole_0(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.64/1.44  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.44  tff(c_388, plain, (![B_74, A_75]: (r1_tarski(k3_xboole_0(B_74, A_75), A_75))), inference(superposition, [status(thm), theory('equality')], [c_313, c_10])).
% 2.64/1.44  tff(c_401, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_388])).
% 2.64/1.44  tff(c_444, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_440, c_401])).
% 2.64/1.44  tff(c_16, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.64/1.44  tff(c_454, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_444, c_16])).
% 2.64/1.44  tff(c_24, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.64/1.44  tff(c_463, plain, (![A_21]: (k5_xboole_0(A_21, A_21)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_454, c_24])).
% 2.64/1.44  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.44  tff(c_608, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.44  tff(c_637, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_608])).
% 2.64/1.44  tff(c_644, plain, (![A_5]: (k4_xboole_0(A_5, A_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_463, c_637])).
% 2.64/1.44  tff(c_44, plain, (![B_55]: (k4_xboole_0(k1_tarski(B_55), k1_tarski(B_55))!=k1_tarski(B_55))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.64/1.44  tff(c_747, plain, (![B_55]: (k1_tarski(B_55)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_644, c_44])).
% 2.64/1.44  tff(c_20, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.64/1.44  tff(c_465, plain, (![A_17]: (k5_xboole_0(A_17, '#skF_1')=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_454, c_20])).
% 2.64/1.44  tff(c_117, plain, (![A_62, B_63]: (r1_tarski(k3_xboole_0(A_62, B_63), A_62))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.44  tff(c_128, plain, (![B_63]: (k3_xboole_0(k1_xboole_0, B_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_16])).
% 2.64/1.44  tff(c_460, plain, (![B_63]: (k3_xboole_0('#skF_1', B_63)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_454, c_454, c_128])).
% 2.64/1.44  tff(c_176, plain, (![B_67, A_68]: (k5_xboole_0(B_67, A_68)=k5_xboole_0(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.64/1.44  tff(c_192, plain, (![A_68]: (k5_xboole_0(k1_xboole_0, A_68)=A_68)), inference(superposition, [status(thm), theory('equality')], [c_176, c_20])).
% 2.64/1.44  tff(c_459, plain, (![A_68]: (k5_xboole_0('#skF_1', A_68)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_454, c_192])).
% 2.64/1.44  tff(c_882, plain, (![A_102, B_103]: (k5_xboole_0(k5_xboole_0(A_102, B_103), k3_xboole_0(A_102, B_103))=k2_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.64/1.44  tff(c_912, plain, (![A_68]: (k5_xboole_0(A_68, k3_xboole_0('#skF_1', A_68))=k2_xboole_0('#skF_1', A_68))), inference(superposition, [status(thm), theory('equality')], [c_459, c_882])).
% 2.64/1.44  tff(c_999, plain, (![A_106]: (k2_xboole_0('#skF_1', A_106)=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_465, c_460, c_912])).
% 2.64/1.44  tff(c_456, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_454, c_440])).
% 2.64/1.44  tff(c_1013, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_999, c_456])).
% 2.64/1.44  tff(c_458, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_454, c_297])).
% 2.64/1.44  tff(c_1139, plain, (k2_tarski('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1013, c_458])).
% 2.64/1.44  tff(c_28, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.64/1.44  tff(c_1162, plain, (k1_tarski('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1139, c_28])).
% 2.64/1.44  tff(c_1170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_747, c_1162])).
% 2.64/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.44  
% 2.64/1.44  Inference rules
% 2.64/1.44  ----------------------
% 2.64/1.44  #Ref     : 0
% 2.64/1.44  #Sup     : 272
% 2.64/1.44  #Fact    : 0
% 2.64/1.44  #Define  : 0
% 2.64/1.44  #Split   : 0
% 2.64/1.44  #Chain   : 0
% 2.64/1.44  #Close   : 0
% 2.64/1.44  
% 2.64/1.44  Ordering : KBO
% 2.64/1.44  
% 2.64/1.44  Simplification rules
% 2.64/1.44  ----------------------
% 2.64/1.44  #Subsume      : 0
% 2.64/1.44  #Demod        : 136
% 2.64/1.44  #Tautology    : 219
% 2.64/1.44  #SimpNegUnit  : 3
% 2.64/1.44  #BackRed      : 17
% 2.64/1.44  
% 2.64/1.44  #Partial instantiations: 0
% 2.64/1.44  #Strategies tried      : 1
% 2.64/1.44  
% 2.64/1.44  Timing (in seconds)
% 2.64/1.44  ----------------------
% 2.64/1.44  Preprocessing        : 0.33
% 2.64/1.44  Parsing              : 0.18
% 2.64/1.44  CNF conversion       : 0.02
% 2.64/1.44  Main loop            : 0.33
% 2.64/1.44  Inferencing          : 0.12
% 2.64/1.44  Reduction            : 0.13
% 2.64/1.44  Demodulation         : 0.10
% 2.64/1.44  BG Simplification    : 0.02
% 2.64/1.44  Subsumption          : 0.04
% 2.64/1.44  Abstraction          : 0.02
% 2.64/1.44  MUC search           : 0.00
% 2.64/1.44  Cooper               : 0.00
% 2.64/1.44  Total                : 0.69
% 2.64/1.45  Index Insertion      : 0.00
% 2.64/1.45  Index Deletion       : 0.00
% 2.64/1.45  Index Matching       : 0.00
% 2.64/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
