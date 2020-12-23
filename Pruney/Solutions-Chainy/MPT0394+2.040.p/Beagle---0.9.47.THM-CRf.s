%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:26 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   48 (  65 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 (  65 expanded)
%              Number of equality atoms :   40 (  56 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_8,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [A_34,B_35] : k3_xboole_0(k1_tarski(A_34),k2_tarski(A_34,B_35)) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_85,plain,(
    ! [A_7] : k3_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_tarski(A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_76])).

tff(c_44,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [B_16] : ~ r1_xboole_0(k1_tarski(B_16),k1_tarski(B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_48,plain,(
    ! [B_16] : k3_xboole_0(k1_tarski(B_16),k1_tarski(B_16)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_16])).

tff(c_105,plain,(
    ! [B_16] : k1_tarski(B_16) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_48])).

tff(c_22,plain,(
    ! [A_21] : k1_setfam_1(k1_tarski(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [A_42,B_43,C_44,D_45] : k2_xboole_0(k1_enumset1(A_42,B_43,C_44),k1_tarski(D_45)) = k2_enumset1(A_42,B_43,C_44,D_45) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_8,B_9,D_45] : k2_xboole_0(k2_tarski(A_8,B_9),k1_tarski(D_45)) = k2_enumset1(A_8,A_8,B_9,D_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_125])).

tff(c_155,plain,(
    ! [A_48,B_49,D_50] : k2_xboole_0(k2_tarski(A_48,B_49),k1_tarski(D_50)) = k1_enumset1(A_48,B_49,D_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_134])).

tff(c_164,plain,(
    ! [A_7,D_50] : k2_xboole_0(k1_tarski(A_7),k1_tarski(D_50)) = k1_enumset1(A_7,A_7,D_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_155])).

tff(c_167,plain,(
    ! [A_7,D_50] : k2_xboole_0(k1_tarski(A_7),k1_tarski(D_50)) = k2_tarski(A_7,D_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_164])).

tff(c_138,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(k1_setfam_1(A_46),k1_setfam_1(B_47)) = k1_setfam_1(k2_xboole_0(A_46,B_47))
      | k1_xboole_0 = B_47
      | k1_xboole_0 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_150,plain,(
    ! [A_46,A_21] :
      ( k1_setfam_1(k2_xboole_0(A_46,k1_tarski(A_21))) = k3_xboole_0(k1_setfam_1(A_46),A_21)
      | k1_tarski(A_21) = k1_xboole_0
      | k1_xboole_0 = A_46 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_138])).

tff(c_196,plain,(
    ! [A_54,A_55] :
      ( k1_setfam_1(k2_xboole_0(A_54,k1_tarski(A_55))) = k3_xboole_0(k1_setfam_1(A_54),A_55)
      | k1_xboole_0 = A_54 ) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_150])).

tff(c_211,plain,(
    ! [A_7,D_50] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_7)),D_50) = k1_setfam_1(k2_tarski(A_7,D_50))
      | k1_tarski(A_7) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_196])).

tff(c_224,plain,(
    ! [A_7,D_50] :
      ( k1_setfam_1(k2_tarski(A_7,D_50)) = k3_xboole_0(A_7,D_50)
      | k1_tarski(A_7) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_211])).

tff(c_225,plain,(
    ! [A_7,D_50] : k1_setfam_1(k2_tarski(A_7,D_50)) = k3_xboole_0(A_7,D_50) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_224])).

tff(c_24,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:28:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.26  
% 1.93/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.27  %$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.93/1.27  
% 1.93/1.27  %Foreground sorts:
% 1.93/1.27  
% 1.93/1.27  
% 1.93/1.27  %Background operators:
% 1.93/1.27  
% 1.93/1.27  
% 1.93/1.27  %Foreground operators:
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.93/1.27  
% 2.04/1.28  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.04/1.28  tff(f_46, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.04/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.04/1.28  tff(f_44, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.04/1.28  tff(f_58, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.04/1.28  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.04/1.28  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.04/1.28  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.04/1.28  tff(f_56, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.04/1.28  tff(f_61, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.04/1.28  tff(c_8, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.28  tff(c_76, plain, (![A_34, B_35]: (k3_xboole_0(k1_tarski(A_34), k2_tarski(A_34, B_35))=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.04/1.28  tff(c_85, plain, (![A_7]: (k3_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_tarski(A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_76])).
% 2.04/1.28  tff(c_44, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.28  tff(c_16, plain, (![B_16]: (~r1_xboole_0(k1_tarski(B_16), k1_tarski(B_16)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.04/1.28  tff(c_48, plain, (![B_16]: (k3_xboole_0(k1_tarski(B_16), k1_tarski(B_16))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_16])).
% 2.04/1.28  tff(c_105, plain, (![B_16]: (k1_tarski(B_16)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_48])).
% 2.04/1.28  tff(c_22, plain, (![A_21]: (k1_setfam_1(k1_tarski(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.28  tff(c_10, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.28  tff(c_12, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.28  tff(c_125, plain, (![A_42, B_43, C_44, D_45]: (k2_xboole_0(k1_enumset1(A_42, B_43, C_44), k1_tarski(D_45))=k2_enumset1(A_42, B_43, C_44, D_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.28  tff(c_134, plain, (![A_8, B_9, D_45]: (k2_xboole_0(k2_tarski(A_8, B_9), k1_tarski(D_45))=k2_enumset1(A_8, A_8, B_9, D_45))), inference(superposition, [status(thm), theory('equality')], [c_10, c_125])).
% 2.04/1.28  tff(c_155, plain, (![A_48, B_49, D_50]: (k2_xboole_0(k2_tarski(A_48, B_49), k1_tarski(D_50))=k1_enumset1(A_48, B_49, D_50))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_134])).
% 2.04/1.28  tff(c_164, plain, (![A_7, D_50]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(D_50))=k1_enumset1(A_7, A_7, D_50))), inference(superposition, [status(thm), theory('equality')], [c_8, c_155])).
% 2.04/1.28  tff(c_167, plain, (![A_7, D_50]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(D_50))=k2_tarski(A_7, D_50))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_164])).
% 2.04/1.28  tff(c_138, plain, (![A_46, B_47]: (k3_xboole_0(k1_setfam_1(A_46), k1_setfam_1(B_47))=k1_setfam_1(k2_xboole_0(A_46, B_47)) | k1_xboole_0=B_47 | k1_xboole_0=A_46)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.28  tff(c_150, plain, (![A_46, A_21]: (k1_setfam_1(k2_xboole_0(A_46, k1_tarski(A_21)))=k3_xboole_0(k1_setfam_1(A_46), A_21) | k1_tarski(A_21)=k1_xboole_0 | k1_xboole_0=A_46)), inference(superposition, [status(thm), theory('equality')], [c_22, c_138])).
% 2.04/1.28  tff(c_196, plain, (![A_54, A_55]: (k1_setfam_1(k2_xboole_0(A_54, k1_tarski(A_55)))=k3_xboole_0(k1_setfam_1(A_54), A_55) | k1_xboole_0=A_54)), inference(negUnitSimplification, [status(thm)], [c_105, c_150])).
% 2.04/1.28  tff(c_211, plain, (![A_7, D_50]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_7)), D_50)=k1_setfam_1(k2_tarski(A_7, D_50)) | k1_tarski(A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_167, c_196])).
% 2.04/1.28  tff(c_224, plain, (![A_7, D_50]: (k1_setfam_1(k2_tarski(A_7, D_50))=k3_xboole_0(A_7, D_50) | k1_tarski(A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_211])).
% 2.04/1.28  tff(c_225, plain, (![A_7, D_50]: (k1_setfam_1(k2_tarski(A_7, D_50))=k3_xboole_0(A_7, D_50))), inference(negUnitSimplification, [status(thm)], [c_105, c_224])).
% 2.04/1.28  tff(c_24, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.04/1.28  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_24])).
% 2.04/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  Inference rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Ref     : 0
% 2.04/1.28  #Sup     : 50
% 2.04/1.28  #Fact    : 0
% 2.04/1.28  #Define  : 0
% 2.04/1.28  #Split   : 0
% 2.04/1.28  #Chain   : 0
% 2.04/1.28  #Close   : 0
% 2.04/1.28  
% 2.04/1.28  Ordering : KBO
% 2.04/1.28  
% 2.04/1.28  Simplification rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Subsume      : 0
% 2.04/1.28  #Demod        : 12
% 2.04/1.28  #Tautology    : 35
% 2.04/1.28  #SimpNegUnit  : 4
% 2.04/1.28  #BackRed      : 2
% 2.04/1.28  
% 2.04/1.28  #Partial instantiations: 0
% 2.04/1.28  #Strategies tried      : 1
% 2.04/1.28  
% 2.04/1.28  Timing (in seconds)
% 2.04/1.28  ----------------------
% 2.04/1.28  Preprocessing        : 0.31
% 2.04/1.28  Parsing              : 0.17
% 2.04/1.28  CNF conversion       : 0.02
% 2.04/1.28  Main loop            : 0.16
% 2.04/1.28  Inferencing          : 0.07
% 2.04/1.28  Reduction            : 0.05
% 2.04/1.28  Demodulation         : 0.04
% 2.04/1.28  BG Simplification    : 0.01
% 2.04/1.28  Subsumption          : 0.02
% 2.04/1.28  Abstraction          : 0.01
% 2.04/1.28  MUC search           : 0.00
% 2.04/1.28  Cooper               : 0.00
% 2.04/1.28  Total                : 0.50
% 2.04/1.28  Index Insertion      : 0.00
% 2.04/1.28  Index Deletion       : 0.00
% 2.04/1.28  Index Matching       : 0.00
% 2.04/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
