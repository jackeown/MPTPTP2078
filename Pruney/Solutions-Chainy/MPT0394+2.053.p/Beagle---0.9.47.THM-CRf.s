%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:27 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   61 (  85 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   57 (  87 expanded)
%              Number of equality atoms :   49 (  70 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = A_36
      | ~ r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_120,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_135,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_120])).

tff(c_138,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_58,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(A_34,B_35)
      | k4_xboole_0(A_34,B_35) != A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ! [B_25] : ~ r1_xboole_0(k1_tarski(B_25),k1_tarski(B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,(
    ! [B_25] : k4_xboole_0(k1_tarski(B_25),k1_tarski(B_25)) != k1_tarski(B_25) ),
    inference(resolution,[status(thm)],[c_58,c_24])).

tff(c_139,plain,(
    ! [B_25] : k1_tarski(B_25) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_62])).

tff(c_28,plain,(
    ! [A_28] : k1_setfam_1(k1_tarski(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20,D_21] : k3_enumset1(A_18,A_18,B_19,C_20,D_21) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_307,plain,(
    ! [D_64,A_67,E_68,C_66,B_65] : k2_xboole_0(k2_enumset1(A_67,B_65,C_66,D_64),k1_tarski(E_68)) = k3_enumset1(A_67,B_65,C_66,D_64,E_68) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_316,plain,(
    ! [A_15,B_16,C_17,E_68] : k3_enumset1(A_15,A_15,B_16,C_17,E_68) = k2_xboole_0(k1_enumset1(A_15,B_16,C_17),k1_tarski(E_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_307])).

tff(c_480,plain,(
    ! [A_77,B_78,C_79,E_80] : k2_xboole_0(k1_enumset1(A_77,B_78,C_79),k1_tarski(E_80)) = k2_enumset1(A_77,B_78,C_79,E_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_316])).

tff(c_492,plain,(
    ! [A_13,B_14,E_80] : k2_xboole_0(k2_tarski(A_13,B_14),k1_tarski(E_80)) = k2_enumset1(A_13,A_13,B_14,E_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_480])).

tff(c_496,plain,(
    ! [A_81,B_82,E_83] : k2_xboole_0(k2_tarski(A_81,B_82),k1_tarski(E_83)) = k1_enumset1(A_81,B_82,E_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_492])).

tff(c_508,plain,(
    ! [A_12,E_83] : k2_xboole_0(k1_tarski(A_12),k1_tarski(E_83)) = k1_enumset1(A_12,A_12,E_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_496])).

tff(c_512,plain,(
    ! [A_84,E_85] : k2_xboole_0(k1_tarski(A_84),k1_tarski(E_85)) = k2_tarski(A_84,E_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_508])).

tff(c_261,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(k1_setfam_1(A_61),k1_setfam_1(B_62)) = k1_setfam_1(k2_xboole_0(A_61,B_62))
      | k1_xboole_0 = B_62
      | k1_xboole_0 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_281,plain,(
    ! [A_28,B_62] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_28),B_62)) = k3_xboole_0(A_28,k1_setfam_1(B_62))
      | k1_xboole_0 = B_62
      | k1_tarski(A_28) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_261])).

tff(c_287,plain,(
    ! [A_28,B_62] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_28),B_62)) = k3_xboole_0(A_28,k1_setfam_1(B_62))
      | k1_xboole_0 = B_62 ) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_281])).

tff(c_518,plain,(
    ! [A_84,E_85] :
      ( k3_xboole_0(A_84,k1_setfam_1(k1_tarski(E_85))) = k1_setfam_1(k2_tarski(A_84,E_85))
      | k1_tarski(E_85) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_287])).

tff(c_538,plain,(
    ! [A_84,E_85] :
      ( k1_setfam_1(k2_tarski(A_84,E_85)) = k3_xboole_0(A_84,E_85)
      | k1_tarski(E_85) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_518])).

tff(c_539,plain,(
    ! [A_84,E_85] : k1_setfam_1(k2_tarski(A_84,E_85)) = k3_xboole_0(A_84,E_85) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_538])).

tff(c_30,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.38  
% 2.34/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.38  %$ r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.34/1.38  
% 2.34/1.38  %Foreground sorts:
% 2.34/1.38  
% 2.34/1.38  
% 2.34/1.38  %Background operators:
% 2.34/1.38  
% 2.34/1.38  
% 2.34/1.38  %Foreground operators:
% 2.34/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.34/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.34/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.34/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.34/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.34/1.38  
% 2.62/1.39  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.62/1.39  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.62/1.39  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.62/1.39  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.62/1.39  tff(f_52, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.62/1.39  tff(f_64, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.62/1.39  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.62/1.39  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.62/1.39  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.62/1.39  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.62/1.39  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 2.62/1.39  tff(f_62, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.62/1.39  tff(f_67, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.62/1.39  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.62/1.39  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.39  tff(c_63, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=A_36 | ~r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.39  tff(c_71, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(resolution, [status(thm)], [c_6, c_63])).
% 2.62/1.39  tff(c_120, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.62/1.39  tff(c_135, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_71, c_120])).
% 2.62/1.39  tff(c_138, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_135])).
% 2.62/1.39  tff(c_58, plain, (![A_34, B_35]: (r1_xboole_0(A_34, B_35) | k4_xboole_0(A_34, B_35)!=A_34)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.39  tff(c_24, plain, (![B_25]: (~r1_xboole_0(k1_tarski(B_25), k1_tarski(B_25)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.62/1.39  tff(c_62, plain, (![B_25]: (k4_xboole_0(k1_tarski(B_25), k1_tarski(B_25))!=k1_tarski(B_25))), inference(resolution, [status(thm)], [c_58, c_24])).
% 2.62/1.39  tff(c_139, plain, (![B_25]: (k1_tarski(B_25)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_62])).
% 2.62/1.39  tff(c_28, plain, (![A_28]: (k1_setfam_1(k1_tarski(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.62/1.39  tff(c_16, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.62/1.39  tff(c_14, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.62/1.39  tff(c_18, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.62/1.39  tff(c_20, plain, (![A_18, B_19, C_20, D_21]: (k3_enumset1(A_18, A_18, B_19, C_20, D_21)=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.62/1.39  tff(c_307, plain, (![D_64, A_67, E_68, C_66, B_65]: (k2_xboole_0(k2_enumset1(A_67, B_65, C_66, D_64), k1_tarski(E_68))=k3_enumset1(A_67, B_65, C_66, D_64, E_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.62/1.39  tff(c_316, plain, (![A_15, B_16, C_17, E_68]: (k3_enumset1(A_15, A_15, B_16, C_17, E_68)=k2_xboole_0(k1_enumset1(A_15, B_16, C_17), k1_tarski(E_68)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_307])).
% 2.62/1.39  tff(c_480, plain, (![A_77, B_78, C_79, E_80]: (k2_xboole_0(k1_enumset1(A_77, B_78, C_79), k1_tarski(E_80))=k2_enumset1(A_77, B_78, C_79, E_80))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_316])).
% 2.62/1.39  tff(c_492, plain, (![A_13, B_14, E_80]: (k2_xboole_0(k2_tarski(A_13, B_14), k1_tarski(E_80))=k2_enumset1(A_13, A_13, B_14, E_80))), inference(superposition, [status(thm), theory('equality')], [c_16, c_480])).
% 2.62/1.39  tff(c_496, plain, (![A_81, B_82, E_83]: (k2_xboole_0(k2_tarski(A_81, B_82), k1_tarski(E_83))=k1_enumset1(A_81, B_82, E_83))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_492])).
% 2.62/1.39  tff(c_508, plain, (![A_12, E_83]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(E_83))=k1_enumset1(A_12, A_12, E_83))), inference(superposition, [status(thm), theory('equality')], [c_14, c_496])).
% 2.62/1.39  tff(c_512, plain, (![A_84, E_85]: (k2_xboole_0(k1_tarski(A_84), k1_tarski(E_85))=k2_tarski(A_84, E_85))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_508])).
% 2.62/1.39  tff(c_261, plain, (![A_61, B_62]: (k3_xboole_0(k1_setfam_1(A_61), k1_setfam_1(B_62))=k1_setfam_1(k2_xboole_0(A_61, B_62)) | k1_xboole_0=B_62 | k1_xboole_0=A_61)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.62/1.39  tff(c_281, plain, (![A_28, B_62]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_28), B_62))=k3_xboole_0(A_28, k1_setfam_1(B_62)) | k1_xboole_0=B_62 | k1_tarski(A_28)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_261])).
% 2.62/1.39  tff(c_287, plain, (![A_28, B_62]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_28), B_62))=k3_xboole_0(A_28, k1_setfam_1(B_62)) | k1_xboole_0=B_62)), inference(negUnitSimplification, [status(thm)], [c_139, c_281])).
% 2.62/1.39  tff(c_518, plain, (![A_84, E_85]: (k3_xboole_0(A_84, k1_setfam_1(k1_tarski(E_85)))=k1_setfam_1(k2_tarski(A_84, E_85)) | k1_tarski(E_85)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_512, c_287])).
% 2.62/1.39  tff(c_538, plain, (![A_84, E_85]: (k1_setfam_1(k2_tarski(A_84, E_85))=k3_xboole_0(A_84, E_85) | k1_tarski(E_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_518])).
% 2.62/1.39  tff(c_539, plain, (![A_84, E_85]: (k1_setfam_1(k2_tarski(A_84, E_85))=k3_xboole_0(A_84, E_85))), inference(negUnitSimplification, [status(thm)], [c_139, c_538])).
% 2.62/1.39  tff(c_30, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.62/1.39  tff(c_618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_539, c_30])).
% 2.62/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.39  
% 2.62/1.39  Inference rules
% 2.62/1.39  ----------------------
% 2.62/1.39  #Ref     : 0
% 2.62/1.39  #Sup     : 137
% 2.62/1.39  #Fact    : 0
% 2.62/1.39  #Define  : 0
% 2.62/1.39  #Split   : 0
% 2.62/1.39  #Chain   : 0
% 2.62/1.39  #Close   : 0
% 2.62/1.39  
% 2.62/1.39  Ordering : KBO
% 2.62/1.39  
% 2.62/1.39  Simplification rules
% 2.62/1.39  ----------------------
% 2.62/1.39  #Subsume      : 2
% 2.62/1.39  #Demod        : 75
% 2.62/1.39  #Tautology    : 85
% 2.62/1.39  #SimpNegUnit  : 16
% 2.62/1.39  #BackRed      : 3
% 2.62/1.39  
% 2.62/1.39  #Partial instantiations: 0
% 2.62/1.39  #Strategies tried      : 1
% 2.62/1.39  
% 2.62/1.39  Timing (in seconds)
% 2.62/1.39  ----------------------
% 2.62/1.39  Preprocessing        : 0.32
% 2.62/1.39  Parsing              : 0.17
% 2.62/1.39  CNF conversion       : 0.02
% 2.62/1.39  Main loop            : 0.26
% 2.62/1.39  Inferencing          : 0.11
% 2.62/1.39  Reduction            : 0.08
% 2.62/1.40  Demodulation         : 0.06
% 2.62/1.40  BG Simplification    : 0.02
% 2.62/1.40  Subsumption          : 0.03
% 2.62/1.40  Abstraction          : 0.02
% 2.62/1.40  MUC search           : 0.00
% 2.62/1.40  Cooper               : 0.00
% 2.62/1.40  Total                : 0.61
% 2.62/1.40  Index Insertion      : 0.00
% 2.62/1.40  Index Deletion       : 0.00
% 2.62/1.40  Index Matching       : 0.00
% 2.62/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
