%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:27 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  81 expanded)
%              Number of equality atoms :   45 (  64 expanded)
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

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

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

tff(c_18,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] : k2_enumset1(A_19,A_19,B_20,C_21) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_210,plain,(
    ! [A_55,B_56,C_57,D_58] : k2_xboole_0(k1_enumset1(A_55,B_56,C_57),k1_tarski(D_58)) = k2_enumset1(A_55,B_56,C_57,D_58) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_219,plain,(
    ! [A_17,B_18,D_58] : k2_xboole_0(k2_tarski(A_17,B_18),k1_tarski(D_58)) = k2_enumset1(A_17,A_17,B_18,D_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_210])).

tff(c_224,plain,(
    ! [A_59,B_60,D_61] : k2_xboole_0(k2_tarski(A_59,B_60),k1_tarski(D_61)) = k1_enumset1(A_59,B_60,D_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_219])).

tff(c_233,plain,(
    ! [A_16,D_61] : k2_xboole_0(k1_tarski(A_16),k1_tarski(D_61)) = k1_enumset1(A_16,A_16,D_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_224])).

tff(c_236,plain,(
    ! [A_16,D_61] : k2_xboole_0(k1_tarski(A_16),k1_tarski(D_61)) = k2_tarski(A_16,D_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_233])).

tff(c_266,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(k1_setfam_1(A_65),k1_setfam_1(B_66)) = k1_setfam_1(k2_xboole_0(A_65,B_66))
      | k1_xboole_0 = B_66
      | k1_xboole_0 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_289,plain,(
    ! [A_65,A_28] :
      ( k1_setfam_1(k2_xboole_0(A_65,k1_tarski(A_28))) = k3_xboole_0(k1_setfam_1(A_65),A_28)
      | k1_tarski(A_28) = k1_xboole_0
      | k1_xboole_0 = A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_266])).

tff(c_354,plain,(
    ! [A_74,A_75] :
      ( k1_setfam_1(k2_xboole_0(A_74,k1_tarski(A_75))) = k3_xboole_0(k1_setfam_1(A_74),A_75)
      | k1_xboole_0 = A_74 ) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_289])).

tff(c_380,plain,(
    ! [A_16,D_61] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_16)),D_61) = k1_setfam_1(k2_tarski(A_16,D_61))
      | k1_tarski(A_16) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_354])).

tff(c_397,plain,(
    ! [A_16,D_61] :
      ( k1_setfam_1(k2_tarski(A_16,D_61)) = k3_xboole_0(A_16,D_61)
      | k1_tarski(A_16) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_380])).

tff(c_398,plain,(
    ! [A_16,D_61] : k1_setfam_1(k2_tarski(A_16,D_61)) = k3_xboole_0(A_16,D_61) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_397])).

tff(c_30,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.29  
% 2.29/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.29  %$ r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.29/1.29  
% 2.29/1.29  %Foreground sorts:
% 2.29/1.29  
% 2.29/1.29  
% 2.29/1.29  %Background operators:
% 2.29/1.29  
% 2.29/1.29  
% 2.29/1.29  %Foreground operators:
% 2.29/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.29/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.29/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.29/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.29/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.29/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.29/1.29  
% 2.29/1.30  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.29/1.30  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.29/1.30  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.29/1.30  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.29/1.30  tff(f_52, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.29/1.30  tff(f_64, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.29/1.30  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.29/1.30  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.29/1.30  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.29/1.30  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.29/1.30  tff(f_62, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.29/1.30  tff(f_67, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.29/1.30  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.29/1.30  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.30  tff(c_63, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=A_36 | ~r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.30  tff(c_71, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(resolution, [status(thm)], [c_6, c_63])).
% 2.29/1.30  tff(c_120, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.30  tff(c_135, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_71, c_120])).
% 2.29/1.30  tff(c_138, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_135])).
% 2.29/1.30  tff(c_58, plain, (![A_34, B_35]: (r1_xboole_0(A_34, B_35) | k4_xboole_0(A_34, B_35)!=A_34)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.30  tff(c_24, plain, (![B_25]: (~r1_xboole_0(k1_tarski(B_25), k1_tarski(B_25)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.30  tff(c_62, plain, (![B_25]: (k4_xboole_0(k1_tarski(B_25), k1_tarski(B_25))!=k1_tarski(B_25))), inference(resolution, [status(thm)], [c_58, c_24])).
% 2.29/1.30  tff(c_139, plain, (![B_25]: (k1_tarski(B_25)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_62])).
% 2.29/1.30  tff(c_28, plain, (![A_28]: (k1_setfam_1(k1_tarski(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.30  tff(c_18, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.29/1.30  tff(c_16, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.29/1.30  tff(c_20, plain, (![A_19, B_20, C_21]: (k2_enumset1(A_19, A_19, B_20, C_21)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.29/1.30  tff(c_210, plain, (![A_55, B_56, C_57, D_58]: (k2_xboole_0(k1_enumset1(A_55, B_56, C_57), k1_tarski(D_58))=k2_enumset1(A_55, B_56, C_57, D_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.30  tff(c_219, plain, (![A_17, B_18, D_58]: (k2_xboole_0(k2_tarski(A_17, B_18), k1_tarski(D_58))=k2_enumset1(A_17, A_17, B_18, D_58))), inference(superposition, [status(thm), theory('equality')], [c_18, c_210])).
% 2.29/1.30  tff(c_224, plain, (![A_59, B_60, D_61]: (k2_xboole_0(k2_tarski(A_59, B_60), k1_tarski(D_61))=k1_enumset1(A_59, B_60, D_61))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_219])).
% 2.29/1.30  tff(c_233, plain, (![A_16, D_61]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(D_61))=k1_enumset1(A_16, A_16, D_61))), inference(superposition, [status(thm), theory('equality')], [c_16, c_224])).
% 2.29/1.30  tff(c_236, plain, (![A_16, D_61]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(D_61))=k2_tarski(A_16, D_61))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_233])).
% 2.29/1.30  tff(c_266, plain, (![A_65, B_66]: (k3_xboole_0(k1_setfam_1(A_65), k1_setfam_1(B_66))=k1_setfam_1(k2_xboole_0(A_65, B_66)) | k1_xboole_0=B_66 | k1_xboole_0=A_65)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.29/1.30  tff(c_289, plain, (![A_65, A_28]: (k1_setfam_1(k2_xboole_0(A_65, k1_tarski(A_28)))=k3_xboole_0(k1_setfam_1(A_65), A_28) | k1_tarski(A_28)=k1_xboole_0 | k1_xboole_0=A_65)), inference(superposition, [status(thm), theory('equality')], [c_28, c_266])).
% 2.29/1.30  tff(c_354, plain, (![A_74, A_75]: (k1_setfam_1(k2_xboole_0(A_74, k1_tarski(A_75)))=k3_xboole_0(k1_setfam_1(A_74), A_75) | k1_xboole_0=A_74)), inference(negUnitSimplification, [status(thm)], [c_139, c_289])).
% 2.29/1.30  tff(c_380, plain, (![A_16, D_61]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_16)), D_61)=k1_setfam_1(k2_tarski(A_16, D_61)) | k1_tarski(A_16)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_236, c_354])).
% 2.29/1.30  tff(c_397, plain, (![A_16, D_61]: (k1_setfam_1(k2_tarski(A_16, D_61))=k3_xboole_0(A_16, D_61) | k1_tarski(A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_380])).
% 2.29/1.30  tff(c_398, plain, (![A_16, D_61]: (k1_setfam_1(k2_tarski(A_16, D_61))=k3_xboole_0(A_16, D_61))), inference(negUnitSimplification, [status(thm)], [c_139, c_397])).
% 2.29/1.30  tff(c_30, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.29/1.30  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_398, c_30])).
% 2.29/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.30  
% 2.29/1.30  Inference rules
% 2.29/1.30  ----------------------
% 2.29/1.30  #Ref     : 0
% 2.29/1.30  #Sup     : 86
% 2.29/1.30  #Fact    : 0
% 2.29/1.30  #Define  : 0
% 2.29/1.30  #Split   : 0
% 2.29/1.30  #Chain   : 0
% 2.29/1.30  #Close   : 0
% 2.29/1.30  
% 2.29/1.30  Ordering : KBO
% 2.29/1.30  
% 2.29/1.30  Simplification rules
% 2.29/1.30  ----------------------
% 2.29/1.30  #Subsume      : 2
% 2.29/1.30  #Demod        : 33
% 2.29/1.30  #Tautology    : 58
% 2.29/1.30  #SimpNegUnit  : 8
% 2.29/1.30  #BackRed      : 2
% 2.29/1.30  
% 2.29/1.30  #Partial instantiations: 0
% 2.29/1.30  #Strategies tried      : 1
% 2.29/1.30  
% 2.29/1.30  Timing (in seconds)
% 2.29/1.30  ----------------------
% 2.29/1.31  Preprocessing        : 0.31
% 2.29/1.31  Parsing              : 0.16
% 2.29/1.31  CNF conversion       : 0.02
% 2.29/1.31  Main loop            : 0.23
% 2.29/1.31  Inferencing          : 0.09
% 2.29/1.31  Reduction            : 0.08
% 2.29/1.31  Demodulation         : 0.06
% 2.29/1.31  BG Simplification    : 0.02
% 2.29/1.31  Subsumption          : 0.03
% 2.29/1.31  Abstraction          : 0.02
% 2.29/1.31  MUC search           : 0.00
% 2.29/1.31  Cooper               : 0.00
% 2.29/1.31  Total                : 0.57
% 2.29/1.31  Index Insertion      : 0.00
% 2.29/1.31  Index Deletion       : 0.00
% 2.29/1.31  Index Matching       : 0.00
% 2.29/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
