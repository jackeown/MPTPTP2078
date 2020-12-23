%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:21 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 139 expanded)
%              Number of leaves         :   31 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :   70 ( 153 expanded)
%              Number of equality atoms :   59 ( 126 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_70,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_78,plain,(
    ! [A_41] : k3_xboole_0(k1_xboole_0,A_41) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_6])).

tff(c_266,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_179,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_218,plain,(
    ! [A_54] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_179])).

tff(c_188,plain,(
    ! [A_41] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_179])).

tff(c_221,plain,(
    ! [A_54,A_41] : k4_xboole_0(k1_xboole_0,A_54) = k4_xboole_0(k1_xboole_0,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_188])).

tff(c_276,plain,(
    ! [A_41,B_58] : k4_xboole_0(k1_xboole_0,A_41) = k3_xboole_0(k1_xboole_0,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_221])).

tff(c_306,plain,(
    ! [A_41] : k4_xboole_0(k1_xboole_0,A_41) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_276])).

tff(c_155,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(A_47,B_48)
      | k4_xboole_0(A_47,B_48) != A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_376,plain,(
    ! [B_68,A_69] :
      ( r1_xboole_0(B_68,A_69)
      | k4_xboole_0(A_69,B_68) != A_69 ) ),
    inference(resolution,[status(thm)],[c_155,c_4])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_658,plain,(
    ! [B_85,A_86] :
      ( k4_xboole_0(B_85,A_86) = B_85
      | k4_xboole_0(A_86,B_85) != A_86 ) ),
    inference(resolution,[status(thm)],[c_376,c_12])).

tff(c_668,plain,(
    ! [A_87] : k4_xboole_0(A_87,k1_xboole_0) = A_87 ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_658])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_683,plain,(
    ! [A_87] : k4_xboole_0(A_87,A_87) = k3_xboole_0(A_87,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_10])).

tff(c_696,plain,(
    ! [A_87] : k4_xboole_0(A_87,A_87) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_683])).

tff(c_28,plain,(
    ! [B_30] : ~ r1_xboole_0(k1_tarski(B_30),k1_tarski(B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_166,plain,(
    ! [B_30] : k4_xboole_0(k1_tarski(B_30),k1_tarski(B_30)) != k1_tarski(B_30) ),
    inference(resolution,[status(thm)],[c_155,c_28])).

tff(c_765,plain,(
    ! [B_30] : k1_tarski(B_30) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_166])).

tff(c_32,plain,(
    ! [A_33] : k1_setfam_1(k1_tarski(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_22,B_23] : k1_enumset1(A_22,A_22,B_23) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_24,B_25,C_26] : k2_enumset1(A_24,A_24,B_25,C_26) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_363,plain,(
    ! [A_64,B_65,C_66,D_67] : k2_xboole_0(k1_enumset1(A_64,B_65,C_66),k1_tarski(D_67)) = k2_enumset1(A_64,B_65,C_66,D_67) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_372,plain,(
    ! [A_22,B_23,D_67] : k2_xboole_0(k2_tarski(A_22,B_23),k1_tarski(D_67)) = k2_enumset1(A_22,A_22,B_23,D_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_363])).

tff(c_752,plain,(
    ! [A_89,B_90,D_91] : k2_xboole_0(k2_tarski(A_89,B_90),k1_tarski(D_91)) = k1_enumset1(A_89,B_90,D_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_372])).

tff(c_761,plain,(
    ! [A_21,D_91] : k2_xboole_0(k1_tarski(A_21),k1_tarski(D_91)) = k1_enumset1(A_21,A_21,D_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_752])).

tff(c_764,plain,(
    ! [A_21,D_91] : k2_xboole_0(k1_tarski(A_21),k1_tarski(D_91)) = k2_tarski(A_21,D_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_761])).

tff(c_481,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(k1_setfam_1(A_74),k1_setfam_1(B_75)) = k1_setfam_1(k2_xboole_0(A_74,B_75))
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_508,plain,(
    ! [A_33,B_75] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_33),B_75)) = k3_xboole_0(A_33,k1_setfam_1(B_75))
      | k1_xboole_0 = B_75
      | k1_tarski(A_33) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_481])).

tff(c_3616,plain,(
    ! [A_147,B_148] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_147),B_148)) = k3_xboole_0(A_147,k1_setfam_1(B_148))
      | k1_xboole_0 = B_148 ) ),
    inference(negUnitSimplification,[status(thm)],[c_765,c_508])).

tff(c_3645,plain,(
    ! [A_21,D_91] :
      ( k3_xboole_0(A_21,k1_setfam_1(k1_tarski(D_91))) = k1_setfam_1(k2_tarski(A_21,D_91))
      | k1_tarski(D_91) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_3616])).

tff(c_3656,plain,(
    ! [A_21,D_91] :
      ( k1_setfam_1(k2_tarski(A_21,D_91)) = k3_xboole_0(A_21,D_91)
      | k1_tarski(D_91) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3645])).

tff(c_3657,plain,(
    ! [A_21,D_91] : k1_setfam_1(k2_tarski(A_21,D_91)) = k3_xboole_0(A_21,D_91) ),
    inference(negUnitSimplification,[status(thm)],[c_765,c_3656])).

tff(c_34,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3657,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:38:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.71  
% 3.93/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.71  %$ r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.93/1.71  
% 3.93/1.71  %Foreground sorts:
% 3.93/1.71  
% 3.93/1.71  
% 3.93/1.71  %Background operators:
% 3.93/1.71  
% 3.93/1.71  
% 3.93/1.71  %Foreground operators:
% 3.93/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.93/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.93/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.93/1.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.93/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.93/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.93/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.93/1.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.93/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.93/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.93/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.71  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.93/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.93/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.93/1.71  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.93/1.71  
% 3.93/1.73  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.93/1.73  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.93/1.73  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.93/1.73  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.93/1.73  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.93/1.73  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.93/1.73  tff(f_58, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 3.93/1.73  tff(f_70, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.93/1.73  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.93/1.73  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.93/1.73  tff(f_51, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.93/1.73  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.93/1.73  tff(f_68, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 3.93/1.73  tff(f_73, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.93/1.73  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.93/1.73  tff(c_62, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.93/1.73  tff(c_78, plain, (![A_41]: (k3_xboole_0(k1_xboole_0, A_41)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62, c_6])).
% 3.93/1.73  tff(c_266, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.93/1.73  tff(c_179, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.93/1.73  tff(c_218, plain, (![A_54]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_54))), inference(superposition, [status(thm), theory('equality')], [c_78, c_179])).
% 3.93/1.73  tff(c_188, plain, (![A_41]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_41))), inference(superposition, [status(thm), theory('equality')], [c_78, c_179])).
% 3.93/1.73  tff(c_221, plain, (![A_54, A_41]: (k4_xboole_0(k1_xboole_0, A_54)=k4_xboole_0(k1_xboole_0, A_41))), inference(superposition, [status(thm), theory('equality')], [c_218, c_188])).
% 3.93/1.73  tff(c_276, plain, (![A_41, B_58]: (k4_xboole_0(k1_xboole_0, A_41)=k3_xboole_0(k1_xboole_0, B_58))), inference(superposition, [status(thm), theory('equality')], [c_266, c_221])).
% 3.93/1.73  tff(c_306, plain, (![A_41]: (k4_xboole_0(k1_xboole_0, A_41)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_276])).
% 3.93/1.73  tff(c_155, plain, (![A_47, B_48]: (r1_xboole_0(A_47, B_48) | k4_xboole_0(A_47, B_48)!=A_47)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.93/1.73  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.93/1.73  tff(c_376, plain, (![B_68, A_69]: (r1_xboole_0(B_68, A_69) | k4_xboole_0(A_69, B_68)!=A_69)), inference(resolution, [status(thm)], [c_155, c_4])).
% 3.93/1.73  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.93/1.73  tff(c_658, plain, (![B_85, A_86]: (k4_xboole_0(B_85, A_86)=B_85 | k4_xboole_0(A_86, B_85)!=A_86)), inference(resolution, [status(thm)], [c_376, c_12])).
% 3.93/1.73  tff(c_668, plain, (![A_87]: (k4_xboole_0(A_87, k1_xboole_0)=A_87)), inference(superposition, [status(thm), theory('equality')], [c_306, c_658])).
% 3.93/1.73  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.93/1.73  tff(c_683, plain, (![A_87]: (k4_xboole_0(A_87, A_87)=k3_xboole_0(A_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_668, c_10])).
% 3.93/1.73  tff(c_696, plain, (![A_87]: (k4_xboole_0(A_87, A_87)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_683])).
% 3.93/1.73  tff(c_28, plain, (![B_30]: (~r1_xboole_0(k1_tarski(B_30), k1_tarski(B_30)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.93/1.73  tff(c_166, plain, (![B_30]: (k4_xboole_0(k1_tarski(B_30), k1_tarski(B_30))!=k1_tarski(B_30))), inference(resolution, [status(thm)], [c_155, c_28])).
% 3.93/1.73  tff(c_765, plain, (![B_30]: (k1_tarski(B_30)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_696, c_166])).
% 3.93/1.73  tff(c_32, plain, (![A_33]: (k1_setfam_1(k1_tarski(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.93/1.73  tff(c_22, plain, (![A_22, B_23]: (k1_enumset1(A_22, A_22, B_23)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.93/1.73  tff(c_20, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.93/1.73  tff(c_24, plain, (![A_24, B_25, C_26]: (k2_enumset1(A_24, A_24, B_25, C_26)=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.93/1.73  tff(c_363, plain, (![A_64, B_65, C_66, D_67]: (k2_xboole_0(k1_enumset1(A_64, B_65, C_66), k1_tarski(D_67))=k2_enumset1(A_64, B_65, C_66, D_67))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.93/1.73  tff(c_372, plain, (![A_22, B_23, D_67]: (k2_xboole_0(k2_tarski(A_22, B_23), k1_tarski(D_67))=k2_enumset1(A_22, A_22, B_23, D_67))), inference(superposition, [status(thm), theory('equality')], [c_22, c_363])).
% 3.93/1.73  tff(c_752, plain, (![A_89, B_90, D_91]: (k2_xboole_0(k2_tarski(A_89, B_90), k1_tarski(D_91))=k1_enumset1(A_89, B_90, D_91))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_372])).
% 3.93/1.73  tff(c_761, plain, (![A_21, D_91]: (k2_xboole_0(k1_tarski(A_21), k1_tarski(D_91))=k1_enumset1(A_21, A_21, D_91))), inference(superposition, [status(thm), theory('equality')], [c_20, c_752])).
% 3.93/1.73  tff(c_764, plain, (![A_21, D_91]: (k2_xboole_0(k1_tarski(A_21), k1_tarski(D_91))=k2_tarski(A_21, D_91))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_761])).
% 3.93/1.73  tff(c_481, plain, (![A_74, B_75]: (k3_xboole_0(k1_setfam_1(A_74), k1_setfam_1(B_75))=k1_setfam_1(k2_xboole_0(A_74, B_75)) | k1_xboole_0=B_75 | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.93/1.73  tff(c_508, plain, (![A_33, B_75]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_33), B_75))=k3_xboole_0(A_33, k1_setfam_1(B_75)) | k1_xboole_0=B_75 | k1_tarski(A_33)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_481])).
% 3.93/1.73  tff(c_3616, plain, (![A_147, B_148]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_147), B_148))=k3_xboole_0(A_147, k1_setfam_1(B_148)) | k1_xboole_0=B_148)), inference(negUnitSimplification, [status(thm)], [c_765, c_508])).
% 3.93/1.73  tff(c_3645, plain, (![A_21, D_91]: (k3_xboole_0(A_21, k1_setfam_1(k1_tarski(D_91)))=k1_setfam_1(k2_tarski(A_21, D_91)) | k1_tarski(D_91)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_764, c_3616])).
% 3.93/1.73  tff(c_3656, plain, (![A_21, D_91]: (k1_setfam_1(k2_tarski(A_21, D_91))=k3_xboole_0(A_21, D_91) | k1_tarski(D_91)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3645])).
% 3.93/1.73  tff(c_3657, plain, (![A_21, D_91]: (k1_setfam_1(k2_tarski(A_21, D_91))=k3_xboole_0(A_21, D_91))), inference(negUnitSimplification, [status(thm)], [c_765, c_3656])).
% 3.93/1.73  tff(c_34, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.93/1.73  tff(c_3662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3657, c_34])).
% 3.93/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.73  
% 3.93/1.73  Inference rules
% 3.93/1.73  ----------------------
% 3.93/1.73  #Ref     : 0
% 3.93/1.73  #Sup     : 898
% 3.93/1.73  #Fact    : 0
% 3.93/1.73  #Define  : 0
% 3.93/1.73  #Split   : 0
% 3.93/1.73  #Chain   : 0
% 3.93/1.73  #Close   : 0
% 3.93/1.73  
% 3.93/1.73  Ordering : KBO
% 3.93/1.73  
% 3.93/1.73  Simplification rules
% 3.93/1.73  ----------------------
% 3.93/1.73  #Subsume      : 149
% 3.93/1.73  #Demod        : 1203
% 3.93/1.73  #Tautology    : 633
% 3.93/1.73  #SimpNegUnit  : 9
% 3.93/1.73  #BackRed      : 2
% 3.93/1.73  
% 3.93/1.73  #Partial instantiations: 0
% 3.93/1.73  #Strategies tried      : 1
% 3.93/1.73  
% 3.93/1.73  Timing (in seconds)
% 3.93/1.73  ----------------------
% 3.93/1.73  Preprocessing        : 0.30
% 3.93/1.73  Parsing              : 0.16
% 3.93/1.73  CNF conversion       : 0.02
% 3.93/1.73  Main loop            : 0.67
% 3.93/1.73  Inferencing          : 0.21
% 3.93/1.73  Reduction            : 0.33
% 3.93/1.73  Demodulation         : 0.28
% 3.93/1.73  BG Simplification    : 0.02
% 3.93/1.73  Subsumption          : 0.08
% 3.93/1.73  Abstraction          : 0.04
% 3.93/1.73  MUC search           : 0.00
% 3.93/1.73  Cooper               : 0.00
% 3.93/1.73  Total                : 1.00
% 3.93/1.73  Index Insertion      : 0.00
% 3.93/1.73  Index Deletion       : 0.00
% 3.93/1.73  Index Matching       : 0.00
% 3.93/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
