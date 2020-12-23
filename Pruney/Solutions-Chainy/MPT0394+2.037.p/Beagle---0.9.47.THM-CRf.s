%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:25 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   48 (  60 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  59 expanded)
%              Number of equality atoms :   39 (  50 expanded)
%              Maximal formula depth    :    7 (   4 average)
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
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

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
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(A_38,B_39)
      | k3_xboole_0(A_38,B_39) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [B_22] : ~ r1_xboole_0(k1_tarski(B_22),k1_tarski(B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_96,plain,(
    ! [B_22] : k3_xboole_0(k1_tarski(B_22),k1_tarski(B_22)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_24])).

tff(c_99,plain,(
    ! [B_22] : k1_tarski(B_22) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_96])).

tff(c_28,plain,(
    ! [A_25] : k1_setfam_1(k1_tarski(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] : k2_enumset1(A_16,A_16,B_17,C_18) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_209,plain,(
    ! [A_56,B_57,C_58,D_59] : k2_xboole_0(k1_enumset1(A_56,B_57,C_58),k1_tarski(D_59)) = k2_enumset1(A_56,B_57,C_58,D_59) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_218,plain,(
    ! [A_14,B_15,D_59] : k2_xboole_0(k2_tarski(A_14,B_15),k1_tarski(D_59)) = k2_enumset1(A_14,A_14,B_15,D_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_209])).

tff(c_279,plain,(
    ! [A_62,B_63,D_64] : k2_xboole_0(k2_tarski(A_62,B_63),k1_tarski(D_64)) = k1_enumset1(A_62,B_63,D_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_218])).

tff(c_288,plain,(
    ! [A_13,D_64] : k2_xboole_0(k1_tarski(A_13),k1_tarski(D_64)) = k1_enumset1(A_13,A_13,D_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_279])).

tff(c_291,plain,(
    ! [A_13,D_64] : k2_xboole_0(k1_tarski(A_13),k1_tarski(D_64)) = k2_tarski(A_13,D_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_288])).

tff(c_311,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(k1_setfam_1(A_67),k1_setfam_1(B_68)) = k1_setfam_1(k2_xboole_0(A_67,B_68))
      | k1_xboole_0 = B_68
      | k1_xboole_0 = A_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_331,plain,(
    ! [A_25,B_68] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_25),B_68)) = k3_xboole_0(A_25,k1_setfam_1(B_68))
      | k1_xboole_0 = B_68
      | k1_tarski(A_25) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_311])).

tff(c_466,plain,(
    ! [A_75,B_76] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_75),B_76)) = k3_xboole_0(A_75,k1_setfam_1(B_76))
      | k1_xboole_0 = B_76 ) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_331])).

tff(c_489,plain,(
    ! [A_13,D_64] :
      ( k3_xboole_0(A_13,k1_setfam_1(k1_tarski(D_64))) = k1_setfam_1(k2_tarski(A_13,D_64))
      | k1_tarski(D_64) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_466])).

tff(c_500,plain,(
    ! [A_13,D_64] :
      ( k1_setfam_1(k2_tarski(A_13,D_64)) = k3_xboole_0(A_13,D_64)
      | k1_tarski(D_64) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_489])).

tff(c_501,plain,(
    ! [A_13,D_64] : k1_setfam_1(k2_tarski(A_13,D_64)) = k3_xboole_0(A_13,D_64) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_500])).

tff(c_30,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:32:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.35  
% 2.39/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.35  %$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.39/1.35  
% 2.39/1.35  %Foreground sorts:
% 2.39/1.35  
% 2.39/1.35  
% 2.39/1.35  %Background operators:
% 2.39/1.35  
% 2.39/1.35  
% 2.39/1.35  %Foreground operators:
% 2.39/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.39/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.39/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.39/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.39/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.39/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.39/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.39/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.39/1.35  
% 2.39/1.37  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.39/1.37  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.39/1.37  tff(f_52, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.39/1.37  tff(f_64, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.39/1.37  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.39/1.37  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.39/1.37  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.39/1.37  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.39/1.37  tff(f_62, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.39/1.37  tff(f_67, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.39/1.37  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.37  tff(c_90, plain, (![A_38, B_39]: (r1_xboole_0(A_38, B_39) | k3_xboole_0(A_38, B_39)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.39/1.37  tff(c_24, plain, (![B_22]: (~r1_xboole_0(k1_tarski(B_22), k1_tarski(B_22)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.39/1.37  tff(c_96, plain, (![B_22]: (k3_xboole_0(k1_tarski(B_22), k1_tarski(B_22))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_90, c_24])).
% 2.39/1.37  tff(c_99, plain, (![B_22]: (k1_tarski(B_22)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_96])).
% 2.39/1.37  tff(c_28, plain, (![A_25]: (k1_setfam_1(k1_tarski(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.39/1.37  tff(c_18, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.39/1.37  tff(c_16, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.39/1.37  tff(c_20, plain, (![A_16, B_17, C_18]: (k2_enumset1(A_16, A_16, B_17, C_18)=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.37  tff(c_209, plain, (![A_56, B_57, C_58, D_59]: (k2_xboole_0(k1_enumset1(A_56, B_57, C_58), k1_tarski(D_59))=k2_enumset1(A_56, B_57, C_58, D_59))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.39/1.37  tff(c_218, plain, (![A_14, B_15, D_59]: (k2_xboole_0(k2_tarski(A_14, B_15), k1_tarski(D_59))=k2_enumset1(A_14, A_14, B_15, D_59))), inference(superposition, [status(thm), theory('equality')], [c_18, c_209])).
% 2.39/1.37  tff(c_279, plain, (![A_62, B_63, D_64]: (k2_xboole_0(k2_tarski(A_62, B_63), k1_tarski(D_64))=k1_enumset1(A_62, B_63, D_64))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_218])).
% 2.39/1.37  tff(c_288, plain, (![A_13, D_64]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(D_64))=k1_enumset1(A_13, A_13, D_64))), inference(superposition, [status(thm), theory('equality')], [c_16, c_279])).
% 2.39/1.37  tff(c_291, plain, (![A_13, D_64]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(D_64))=k2_tarski(A_13, D_64))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_288])).
% 2.39/1.37  tff(c_311, plain, (![A_67, B_68]: (k3_xboole_0(k1_setfam_1(A_67), k1_setfam_1(B_68))=k1_setfam_1(k2_xboole_0(A_67, B_68)) | k1_xboole_0=B_68 | k1_xboole_0=A_67)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.39/1.37  tff(c_331, plain, (![A_25, B_68]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_25), B_68))=k3_xboole_0(A_25, k1_setfam_1(B_68)) | k1_xboole_0=B_68 | k1_tarski(A_25)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_311])).
% 2.39/1.37  tff(c_466, plain, (![A_75, B_76]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_75), B_76))=k3_xboole_0(A_75, k1_setfam_1(B_76)) | k1_xboole_0=B_76)), inference(negUnitSimplification, [status(thm)], [c_99, c_331])).
% 2.39/1.37  tff(c_489, plain, (![A_13, D_64]: (k3_xboole_0(A_13, k1_setfam_1(k1_tarski(D_64)))=k1_setfam_1(k2_tarski(A_13, D_64)) | k1_tarski(D_64)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_291, c_466])).
% 2.39/1.37  tff(c_500, plain, (![A_13, D_64]: (k1_setfam_1(k2_tarski(A_13, D_64))=k3_xboole_0(A_13, D_64) | k1_tarski(D_64)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_489])).
% 2.39/1.37  tff(c_501, plain, (![A_13, D_64]: (k1_setfam_1(k2_tarski(A_13, D_64))=k3_xboole_0(A_13, D_64))), inference(negUnitSimplification, [status(thm)], [c_99, c_500])).
% 2.39/1.37  tff(c_30, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.37  tff(c_551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_501, c_30])).
% 2.39/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.37  
% 2.39/1.37  Inference rules
% 2.39/1.37  ----------------------
% 2.39/1.37  #Ref     : 0
% 2.39/1.37  #Sup     : 117
% 2.39/1.37  #Fact    : 0
% 2.39/1.37  #Define  : 0
% 2.39/1.37  #Split   : 0
% 2.39/1.37  #Chain   : 0
% 2.39/1.37  #Close   : 0
% 2.39/1.37  
% 2.39/1.37  Ordering : KBO
% 2.39/1.37  
% 2.39/1.37  Simplification rules
% 2.39/1.37  ----------------------
% 2.39/1.37  #Subsume      : 6
% 2.39/1.37  #Demod        : 59
% 2.39/1.37  #Tautology    : 77
% 2.39/1.37  #SimpNegUnit  : 7
% 2.39/1.37  #BackRed      : 3
% 2.39/1.37  
% 2.39/1.37  #Partial instantiations: 0
% 2.39/1.37  #Strategies tried      : 1
% 2.39/1.37  
% 2.39/1.37  Timing (in seconds)
% 2.39/1.37  ----------------------
% 2.51/1.37  Preprocessing        : 0.32
% 2.51/1.37  Parsing              : 0.17
% 2.51/1.37  CNF conversion       : 0.02
% 2.51/1.37  Main loop            : 0.25
% 2.51/1.37  Inferencing          : 0.10
% 2.51/1.37  Reduction            : 0.08
% 2.51/1.37  Demodulation         : 0.06
% 2.51/1.37  BG Simplification    : 0.02
% 2.51/1.37  Subsumption          : 0.03
% 2.51/1.37  Abstraction          : 0.02
% 2.51/1.37  MUC search           : 0.00
% 2.51/1.37  Cooper               : 0.00
% 2.51/1.37  Total                : 0.60
% 2.51/1.37  Index Insertion      : 0.00
% 2.51/1.37  Index Deletion       : 0.00
% 2.51/1.37  Index Matching       : 0.00
% 2.51/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
