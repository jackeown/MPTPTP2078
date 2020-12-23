%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:25 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
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
%$ r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [B_23] : ~ r1_xboole_0(k1_tarski(B_23),k1_tarski(B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    ! [B_23] : k3_xboole_0(k1_tarski(B_23),k1_tarski(B_23)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_20])).

tff(c_65,plain,(
    ! [B_23] : k1_tarski(B_23) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_62])).

tff(c_24,plain,(
    ! [A_26] : k1_setfam_1(k1_tarski(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19] : k2_enumset1(A_17,A_17,B_18,C_19) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_114,plain,(
    ! [A_44,B_45,C_46,D_47] : k2_xboole_0(k1_enumset1(A_44,B_45,C_46),k1_tarski(D_47)) = k2_enumset1(A_44,B_45,C_46,D_47) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    ! [A_15,B_16,D_47] : k2_xboole_0(k2_tarski(A_15,B_16),k1_tarski(D_47)) = k2_enumset1(A_15,A_15,B_16,D_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_114])).

tff(c_127,plain,(
    ! [A_48,B_49,D_50] : k2_xboole_0(k2_tarski(A_48,B_49),k1_tarski(D_50)) = k1_enumset1(A_48,B_49,D_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_123])).

tff(c_136,plain,(
    ! [A_14,D_50] : k2_xboole_0(k1_tarski(A_14),k1_tarski(D_50)) = k1_enumset1(A_14,A_14,D_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_127])).

tff(c_139,plain,(
    ! [A_14,D_50] : k2_xboole_0(k1_tarski(A_14),k1_tarski(D_50)) = k2_tarski(A_14,D_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_136])).

tff(c_159,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(k1_setfam_1(A_53),k1_setfam_1(B_54)) = k1_setfam_1(k2_xboole_0(A_53,B_54))
      | k1_xboole_0 = B_54
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_179,plain,(
    ! [A_53,A_26] :
      ( k1_setfam_1(k2_xboole_0(A_53,k1_tarski(A_26))) = k3_xboole_0(k1_setfam_1(A_53),A_26)
      | k1_tarski(A_26) = k1_xboole_0
      | k1_xboole_0 = A_53 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_159])).

tff(c_254,plain,(
    ! [A_63,A_64] :
      ( k1_setfam_1(k2_xboole_0(A_63,k1_tarski(A_64))) = k3_xboole_0(k1_setfam_1(A_63),A_64)
      | k1_xboole_0 = A_63 ) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_179])).

tff(c_280,plain,(
    ! [A_14,D_50] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_14)),D_50) = k1_setfam_1(k2_tarski(A_14,D_50))
      | k1_tarski(A_14) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_254])).

tff(c_297,plain,(
    ! [A_14,D_50] :
      ( k1_setfam_1(k2_tarski(A_14,D_50)) = k3_xboole_0(A_14,D_50)
      | k1_tarski(A_14) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_280])).

tff(c_298,plain,(
    ! [A_14,D_50] : k1_setfam_1(k2_tarski(A_14,D_50)) = k3_xboole_0(A_14,D_50) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_297])).

tff(c_26,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:40:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.26  %$ r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.03/1.26  
% 2.03/1.26  %Foreground sorts:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Background operators:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Foreground operators:
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.03/1.26  
% 2.03/1.27  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.03/1.27  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.03/1.27  tff(f_48, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.03/1.27  tff(f_60, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.03/1.27  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.03/1.27  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.03/1.27  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.03/1.27  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.03/1.27  tff(f_58, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.03/1.27  tff(f_63, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.03/1.27  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.27  tff(c_56, plain, (![A_33, B_34]: (r1_xboole_0(A_33, B_34) | k3_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.27  tff(c_20, plain, (![B_23]: (~r1_xboole_0(k1_tarski(B_23), k1_tarski(B_23)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.27  tff(c_62, plain, (![B_23]: (k3_xboole_0(k1_tarski(B_23), k1_tarski(B_23))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_20])).
% 2.03/1.27  tff(c_65, plain, (![B_23]: (k1_tarski(B_23)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_62])).
% 2.03/1.27  tff(c_24, plain, (![A_26]: (k1_setfam_1(k1_tarski(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.03/1.27  tff(c_14, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.27  tff(c_12, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.03/1.27  tff(c_16, plain, (![A_17, B_18, C_19]: (k2_enumset1(A_17, A_17, B_18, C_19)=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.03/1.27  tff(c_114, plain, (![A_44, B_45, C_46, D_47]: (k2_xboole_0(k1_enumset1(A_44, B_45, C_46), k1_tarski(D_47))=k2_enumset1(A_44, B_45, C_46, D_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.03/1.27  tff(c_123, plain, (![A_15, B_16, D_47]: (k2_xboole_0(k2_tarski(A_15, B_16), k1_tarski(D_47))=k2_enumset1(A_15, A_15, B_16, D_47))), inference(superposition, [status(thm), theory('equality')], [c_14, c_114])).
% 2.03/1.27  tff(c_127, plain, (![A_48, B_49, D_50]: (k2_xboole_0(k2_tarski(A_48, B_49), k1_tarski(D_50))=k1_enumset1(A_48, B_49, D_50))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_123])).
% 2.03/1.27  tff(c_136, plain, (![A_14, D_50]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(D_50))=k1_enumset1(A_14, A_14, D_50))), inference(superposition, [status(thm), theory('equality')], [c_12, c_127])).
% 2.03/1.27  tff(c_139, plain, (![A_14, D_50]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(D_50))=k2_tarski(A_14, D_50))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_136])).
% 2.03/1.27  tff(c_159, plain, (![A_53, B_54]: (k3_xboole_0(k1_setfam_1(A_53), k1_setfam_1(B_54))=k1_setfam_1(k2_xboole_0(A_53, B_54)) | k1_xboole_0=B_54 | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.03/1.27  tff(c_179, plain, (![A_53, A_26]: (k1_setfam_1(k2_xboole_0(A_53, k1_tarski(A_26)))=k3_xboole_0(k1_setfam_1(A_53), A_26) | k1_tarski(A_26)=k1_xboole_0 | k1_xboole_0=A_53)), inference(superposition, [status(thm), theory('equality')], [c_24, c_159])).
% 2.03/1.27  tff(c_254, plain, (![A_63, A_64]: (k1_setfam_1(k2_xboole_0(A_63, k1_tarski(A_64)))=k3_xboole_0(k1_setfam_1(A_63), A_64) | k1_xboole_0=A_63)), inference(negUnitSimplification, [status(thm)], [c_65, c_179])).
% 2.03/1.27  tff(c_280, plain, (![A_14, D_50]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_14)), D_50)=k1_setfam_1(k2_tarski(A_14, D_50)) | k1_tarski(A_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_139, c_254])).
% 2.03/1.27  tff(c_297, plain, (![A_14, D_50]: (k1_setfam_1(k2_tarski(A_14, D_50))=k3_xboole_0(A_14, D_50) | k1_tarski(A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_280])).
% 2.03/1.27  tff(c_298, plain, (![A_14, D_50]: (k1_setfam_1(k2_tarski(A_14, D_50))=k3_xboole_0(A_14, D_50))), inference(negUnitSimplification, [status(thm)], [c_65, c_297])).
% 2.03/1.27  tff(c_26, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.03/1.27  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_298, c_26])).
% 2.03/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.27  
% 2.03/1.27  Inference rules
% 2.03/1.27  ----------------------
% 2.03/1.27  #Ref     : 0
% 2.03/1.27  #Sup     : 63
% 2.03/1.27  #Fact    : 0
% 2.03/1.27  #Define  : 0
% 2.03/1.27  #Split   : 0
% 2.03/1.27  #Chain   : 0
% 2.03/1.27  #Close   : 0
% 2.03/1.27  
% 2.03/1.27  Ordering : KBO
% 2.03/1.27  
% 2.03/1.27  Simplification rules
% 2.03/1.27  ----------------------
% 2.03/1.27  #Subsume      : 2
% 2.03/1.27  #Demod        : 24
% 2.03/1.27  #Tautology    : 41
% 2.03/1.27  #SimpNegUnit  : 8
% 2.03/1.27  #BackRed      : 1
% 2.03/1.27  
% 2.03/1.27  #Partial instantiations: 0
% 2.03/1.27  #Strategies tried      : 1
% 2.03/1.27  
% 2.03/1.27  Timing (in seconds)
% 2.03/1.27  ----------------------
% 2.03/1.27  Preprocessing        : 0.29
% 2.03/1.27  Parsing              : 0.16
% 2.03/1.27  CNF conversion       : 0.02
% 2.03/1.27  Main loop            : 0.19
% 2.03/1.27  Inferencing          : 0.08
% 2.03/1.27  Reduction            : 0.06
% 2.03/1.27  Demodulation         : 0.05
% 2.03/1.27  BG Simplification    : 0.02
% 2.03/1.27  Subsumption          : 0.03
% 2.03/1.27  Abstraction          : 0.02
% 2.03/1.27  MUC search           : 0.00
% 2.03/1.27  Cooper               : 0.00
% 2.03/1.27  Total                : 0.51
% 2.03/1.27  Index Insertion      : 0.00
% 2.03/1.27  Index Deletion       : 0.00
% 2.03/1.28  Index Matching       : 0.00
% 2.03/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
