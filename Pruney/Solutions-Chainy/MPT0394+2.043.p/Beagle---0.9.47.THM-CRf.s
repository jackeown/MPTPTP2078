%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:26 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 156 expanded)
%              Number of leaves         :   28 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :   67 ( 191 expanded)
%              Number of equality atoms :   59 ( 158 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = A_37
      | k3_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_88,c_10])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_125,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_180,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,k4_xboole_0(A_53,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_125])).

tff(c_218,plain,(
    ! [A_59] : k3_xboole_0(A_59,k4_xboole_0(A_59,k1_xboole_0)) = k4_xboole_0(A_59,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_180])).

tff(c_231,plain,(
    ! [A_37] :
      ( k4_xboole_0(A_37,k1_xboole_0) = k3_xboole_0(A_37,A_37)
      | k3_xboole_0(A_37,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_218])).

tff(c_238,plain,(
    ! [A_60] : k4_xboole_0(A_60,k1_xboole_0) = k3_xboole_0(A_60,A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_231])).

tff(c_256,plain,(
    ! [A_60] :
      ( k3_xboole_0(A_60,A_60) = A_60
      | k3_xboole_0(A_60,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_95])).

tff(c_275,plain,(
    ! [A_60] : k3_xboole_0(A_60,A_60) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_256])).

tff(c_236,plain,(
    ! [A_37] : k4_xboole_0(A_37,k1_xboole_0) = k3_xboole_0(A_37,A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_231])).

tff(c_307,plain,(
    ! [A_62] : k4_xboole_0(A_62,k1_xboole_0) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_236])).

tff(c_319,plain,(
    ! [A_62] : k4_xboole_0(A_62,A_62) = k3_xboole_0(A_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_8])).

tff(c_333,plain,(
    ! [A_62] : k4_xboole_0(A_62,A_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_319])).

tff(c_67,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [B_21] : ~ r1_xboole_0(k1_tarski(B_21),k1_tarski(B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,(
    ! [B_21] : k4_xboole_0(k1_tarski(B_21),k1_tarski(B_21)) != k1_tarski(B_21) ),
    inference(resolution,[status(thm)],[c_67,c_24])).

tff(c_364,plain,(
    ! [B_21] : k1_tarski(B_21) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_75])).

tff(c_28,plain,(
    ! [A_24] : k1_setfam_1(k1_tarski(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_205,plain,(
    ! [A_55,B_56,C_57,D_58] : k2_xboole_0(k1_enumset1(A_55,B_56,C_57),k1_tarski(D_58)) = k2_enumset1(A_55,B_56,C_57,D_58) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_214,plain,(
    ! [A_13,B_14,D_58] : k2_xboole_0(k2_tarski(A_13,B_14),k1_tarski(D_58)) = k2_enumset1(A_13,A_13,B_14,D_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_205])).

tff(c_406,plain,(
    ! [A_67,B_68,D_69] : k2_xboole_0(k2_tarski(A_67,B_68),k1_tarski(D_69)) = k1_enumset1(A_67,B_68,D_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_214])).

tff(c_415,plain,(
    ! [A_12,D_69] : k2_xboole_0(k1_tarski(A_12),k1_tarski(D_69)) = k1_enumset1(A_12,A_12,D_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_406])).

tff(c_456,plain,(
    ! [A_73,D_74] : k2_xboole_0(k1_tarski(A_73),k1_tarski(D_74)) = k2_tarski(A_73,D_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_415])).

tff(c_338,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(k1_setfam_1(A_63),k1_setfam_1(B_64)) = k1_setfam_1(k2_xboole_0(A_63,B_64))
      | k1_xboole_0 = B_64
      | k1_xboole_0 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_358,plain,(
    ! [A_24,B_64] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_24),B_64)) = k3_xboole_0(A_24,k1_setfam_1(B_64))
      | k1_xboole_0 = B_64
      | k1_tarski(A_24) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_338])).

tff(c_419,plain,(
    ! [A_24,B_64] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_24),B_64)) = k3_xboole_0(A_24,k1_setfam_1(B_64))
      | k1_xboole_0 = B_64 ) ),
    inference(negUnitSimplification,[status(thm)],[c_364,c_358])).

tff(c_462,plain,(
    ! [A_73,D_74] :
      ( k3_xboole_0(A_73,k1_setfam_1(k1_tarski(D_74))) = k1_setfam_1(k2_tarski(A_73,D_74))
      | k1_tarski(D_74) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_419])).

tff(c_475,plain,(
    ! [A_73,D_74] :
      ( k1_setfam_1(k2_tarski(A_73,D_74)) = k3_xboole_0(A_73,D_74)
      | k1_tarski(D_74) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_462])).

tff(c_476,plain,(
    ! [A_73,D_74] : k1_setfam_1(k2_tarski(A_73,D_74)) = k3_xboole_0(A_73,D_74) ),
    inference(negUnitSimplification,[status(thm)],[c_364,c_475])).

tff(c_30,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:26:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.33  
% 2.47/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.33  %$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.47/1.33  
% 2.47/1.33  %Foreground sorts:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Background operators:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Foreground operators:
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.47/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.47/1.33  
% 2.47/1.34  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.47/1.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.47/1.34  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.47/1.34  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.47/1.34  tff(f_52, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.47/1.34  tff(f_64, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.47/1.34  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.47/1.34  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.47/1.34  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.47/1.34  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.47/1.34  tff(f_62, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.47/1.34  tff(f_67, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.47/1.34  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.34  tff(c_88, plain, (![A_37, B_38]: (r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.34  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.34  tff(c_95, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=A_37 | k3_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_88, c_10])).
% 2.47/1.34  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.34  tff(c_125, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.34  tff(c_180, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k3_xboole_0(A_53, k4_xboole_0(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_125])).
% 2.47/1.34  tff(c_218, plain, (![A_59]: (k3_xboole_0(A_59, k4_xboole_0(A_59, k1_xboole_0))=k4_xboole_0(A_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_180])).
% 2.47/1.34  tff(c_231, plain, (![A_37]: (k4_xboole_0(A_37, k1_xboole_0)=k3_xboole_0(A_37, A_37) | k3_xboole_0(A_37, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_95, c_218])).
% 2.47/1.34  tff(c_238, plain, (![A_60]: (k4_xboole_0(A_60, k1_xboole_0)=k3_xboole_0(A_60, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_231])).
% 2.47/1.34  tff(c_256, plain, (![A_60]: (k3_xboole_0(A_60, A_60)=A_60 | k3_xboole_0(A_60, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_238, c_95])).
% 2.47/1.34  tff(c_275, plain, (![A_60]: (k3_xboole_0(A_60, A_60)=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_256])).
% 2.47/1.34  tff(c_236, plain, (![A_37]: (k4_xboole_0(A_37, k1_xboole_0)=k3_xboole_0(A_37, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_231])).
% 2.47/1.34  tff(c_307, plain, (![A_62]: (k4_xboole_0(A_62, k1_xboole_0)=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_275, c_236])).
% 2.47/1.34  tff(c_319, plain, (![A_62]: (k4_xboole_0(A_62, A_62)=k3_xboole_0(A_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_307, c_8])).
% 2.47/1.34  tff(c_333, plain, (![A_62]: (k4_xboole_0(A_62, A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_319])).
% 2.47/1.34  tff(c_67, plain, (![A_33, B_34]: (r1_xboole_0(A_33, B_34) | k4_xboole_0(A_33, B_34)!=A_33)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.34  tff(c_24, plain, (![B_21]: (~r1_xboole_0(k1_tarski(B_21), k1_tarski(B_21)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.47/1.34  tff(c_75, plain, (![B_21]: (k4_xboole_0(k1_tarski(B_21), k1_tarski(B_21))!=k1_tarski(B_21))), inference(resolution, [status(thm)], [c_67, c_24])).
% 2.47/1.34  tff(c_364, plain, (![B_21]: (k1_tarski(B_21)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_333, c_75])).
% 2.47/1.34  tff(c_28, plain, (![A_24]: (k1_setfam_1(k1_tarski(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.34  tff(c_18, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.47/1.34  tff(c_16, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.47/1.34  tff(c_20, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.34  tff(c_205, plain, (![A_55, B_56, C_57, D_58]: (k2_xboole_0(k1_enumset1(A_55, B_56, C_57), k1_tarski(D_58))=k2_enumset1(A_55, B_56, C_57, D_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.47/1.34  tff(c_214, plain, (![A_13, B_14, D_58]: (k2_xboole_0(k2_tarski(A_13, B_14), k1_tarski(D_58))=k2_enumset1(A_13, A_13, B_14, D_58))), inference(superposition, [status(thm), theory('equality')], [c_18, c_205])).
% 2.47/1.34  tff(c_406, plain, (![A_67, B_68, D_69]: (k2_xboole_0(k2_tarski(A_67, B_68), k1_tarski(D_69))=k1_enumset1(A_67, B_68, D_69))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_214])).
% 2.47/1.34  tff(c_415, plain, (![A_12, D_69]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(D_69))=k1_enumset1(A_12, A_12, D_69))), inference(superposition, [status(thm), theory('equality')], [c_16, c_406])).
% 2.47/1.34  tff(c_456, plain, (![A_73, D_74]: (k2_xboole_0(k1_tarski(A_73), k1_tarski(D_74))=k2_tarski(A_73, D_74))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_415])).
% 2.47/1.34  tff(c_338, plain, (![A_63, B_64]: (k3_xboole_0(k1_setfam_1(A_63), k1_setfam_1(B_64))=k1_setfam_1(k2_xboole_0(A_63, B_64)) | k1_xboole_0=B_64 | k1_xboole_0=A_63)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.47/1.34  tff(c_358, plain, (![A_24, B_64]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_24), B_64))=k3_xboole_0(A_24, k1_setfam_1(B_64)) | k1_xboole_0=B_64 | k1_tarski(A_24)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_338])).
% 2.47/1.34  tff(c_419, plain, (![A_24, B_64]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_24), B_64))=k3_xboole_0(A_24, k1_setfam_1(B_64)) | k1_xboole_0=B_64)), inference(negUnitSimplification, [status(thm)], [c_364, c_358])).
% 2.47/1.34  tff(c_462, plain, (![A_73, D_74]: (k3_xboole_0(A_73, k1_setfam_1(k1_tarski(D_74)))=k1_setfam_1(k2_tarski(A_73, D_74)) | k1_tarski(D_74)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_456, c_419])).
% 2.47/1.34  tff(c_475, plain, (![A_73, D_74]: (k1_setfam_1(k2_tarski(A_73, D_74))=k3_xboole_0(A_73, D_74) | k1_tarski(D_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_462])).
% 2.47/1.34  tff(c_476, plain, (![A_73, D_74]: (k1_setfam_1(k2_tarski(A_73, D_74))=k3_xboole_0(A_73, D_74))), inference(negUnitSimplification, [status(thm)], [c_364, c_475])).
% 2.47/1.34  tff(c_30, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.47/1.34  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_476, c_30])).
% 2.47/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  Inference rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Ref     : 0
% 2.47/1.34  #Sup     : 109
% 2.47/1.34  #Fact    : 0
% 2.47/1.34  #Define  : 0
% 2.47/1.34  #Split   : 0
% 2.47/1.34  #Chain   : 0
% 2.47/1.34  #Close   : 0
% 2.47/1.34  
% 2.47/1.34  Ordering : KBO
% 2.47/1.34  
% 2.47/1.34  Simplification rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Subsume      : 2
% 2.47/1.34  #Demod        : 56
% 2.47/1.34  #Tautology    : 75
% 2.47/1.34  #SimpNegUnit  : 3
% 2.47/1.35  #BackRed      : 6
% 2.47/1.35  
% 2.47/1.35  #Partial instantiations: 0
% 2.47/1.35  #Strategies tried      : 1
% 2.47/1.35  
% 2.47/1.35  Timing (in seconds)
% 2.47/1.35  ----------------------
% 2.61/1.35  Preprocessing        : 0.32
% 2.61/1.35  Parsing              : 0.17
% 2.61/1.35  CNF conversion       : 0.02
% 2.61/1.35  Main loop            : 0.25
% 2.61/1.35  Inferencing          : 0.10
% 2.61/1.35  Reduction            : 0.08
% 2.61/1.35  Demodulation         : 0.06
% 2.61/1.35  BG Simplification    : 0.02
% 2.61/1.35  Subsumption          : 0.03
% 2.61/1.35  Abstraction          : 0.02
% 2.61/1.35  MUC search           : 0.00
% 2.61/1.35  Cooper               : 0.00
% 2.61/1.35  Total                : 0.60
% 2.61/1.35  Index Insertion      : 0.00
% 2.61/1.35  Index Deletion       : 0.00
% 2.61/1.35  Index Matching       : 0.00
% 2.61/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
