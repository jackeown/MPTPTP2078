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
% DateTime   : Thu Dec  3 09:59:29 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   33 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  67 expanded)
%              Number of equality atoms :   22 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_75,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

tff(c_36,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_1'(A_41),A_41)
      | v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [B_79,A_80] :
      ( ~ r2_hidden(B_79,A_80)
      | k4_xboole_0(A_80,k1_tarski(B_79)) != A_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_145,plain,(
    ! [B_81] : ~ r2_hidden(B_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_135])).

tff(c_150,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_145])).

tff(c_40,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_151,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k4_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_160,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_151])).

tff(c_163,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_160])).

tff(c_28,plain,(
    ! [A_37,B_38] : k6_subset_1(A_37,B_38) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    ! [A_59,B_61] :
      ( k6_subset_1(k4_relat_1(A_59),k4_relat_1(B_61)) = k4_relat_1(k6_subset_1(A_59,B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_240,plain,(
    ! [A_101,B_102] :
      ( k4_xboole_0(k4_relat_1(A_101),k4_relat_1(B_102)) = k4_relat_1(k4_xboole_0(A_101,B_102))
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_38])).

tff(c_247,plain,(
    ! [B_102] :
      ( k4_relat_1(k4_xboole_0(B_102,B_102)) = k1_xboole_0
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_163])).

tff(c_256,plain,(
    ! [B_102] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_247])).

tff(c_261,plain,(
    ! [B_103] :
      ( ~ v1_relat_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_256])).

tff(c_263,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_150,c_261])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.27  
% 1.81/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.27  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.81/1.27  
% 1.81/1.27  %Foreground sorts:
% 1.81/1.27  
% 1.81/1.27  
% 1.81/1.27  %Background operators:
% 1.81/1.27  
% 1.81/1.27  
% 1.81/1.27  %Foreground operators:
% 1.81/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.81/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.81/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.81/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.81/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.81/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.81/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.81/1.27  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.81/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.81/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.81/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.81/1.27  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.81/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.81/1.27  
% 1.81/1.28  tff(f_66, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.81/1.28  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.81/1.28  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.81/1.28  tff(f_75, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 1.81/1.28  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.81/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.81/1.28  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.81/1.28  tff(f_54, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.81/1.28  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 1.81/1.28  tff(c_36, plain, (![A_41]: (r2_hidden('#skF_1'(A_41), A_41) | v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.81/1.28  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.28  tff(c_135, plain, (![B_79, A_80]: (~r2_hidden(B_79, A_80) | k4_xboole_0(A_80, k1_tarski(B_79))!=A_80)), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.28  tff(c_145, plain, (![B_81]: (~r2_hidden(B_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_135])).
% 1.81/1.28  tff(c_150, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_145])).
% 1.81/1.28  tff(c_40, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.81/1.28  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.28  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.81/1.28  tff(c_151, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k4_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.28  tff(c_160, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_151])).
% 1.81/1.28  tff(c_163, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_160])).
% 1.81/1.28  tff(c_28, plain, (![A_37, B_38]: (k6_subset_1(A_37, B_38)=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.81/1.28  tff(c_38, plain, (![A_59, B_61]: (k6_subset_1(k4_relat_1(A_59), k4_relat_1(B_61))=k4_relat_1(k6_subset_1(A_59, B_61)) | ~v1_relat_1(B_61) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.81/1.28  tff(c_240, plain, (![A_101, B_102]: (k4_xboole_0(k4_relat_1(A_101), k4_relat_1(B_102))=k4_relat_1(k4_xboole_0(A_101, B_102)) | ~v1_relat_1(B_102) | ~v1_relat_1(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_38])).
% 1.81/1.28  tff(c_247, plain, (![B_102]: (k4_relat_1(k4_xboole_0(B_102, B_102))=k1_xboole_0 | ~v1_relat_1(B_102) | ~v1_relat_1(B_102))), inference(superposition, [status(thm), theory('equality')], [c_240, c_163])).
% 1.81/1.28  tff(c_256, plain, (![B_102]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_102) | ~v1_relat_1(B_102))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_247])).
% 1.81/1.28  tff(c_261, plain, (![B_103]: (~v1_relat_1(B_103) | ~v1_relat_1(B_103))), inference(negUnitSimplification, [status(thm)], [c_40, c_256])).
% 1.81/1.28  tff(c_263, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_150, c_261])).
% 1.81/1.28  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_263])).
% 1.81/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.28  
% 1.81/1.28  Inference rules
% 1.81/1.28  ----------------------
% 1.81/1.28  #Ref     : 1
% 1.81/1.28  #Sup     : 49
% 1.81/1.28  #Fact    : 0
% 1.81/1.28  #Define  : 0
% 1.81/1.28  #Split   : 0
% 1.81/1.28  #Chain   : 0
% 1.81/1.28  #Close   : 0
% 1.81/1.28  
% 1.81/1.28  Ordering : KBO
% 1.81/1.28  
% 1.81/1.28  Simplification rules
% 1.81/1.28  ----------------------
% 1.81/1.28  #Subsume      : 1
% 1.81/1.28  #Demod        : 7
% 1.81/1.28  #Tautology    : 37
% 1.81/1.28  #SimpNegUnit  : 2
% 1.81/1.28  #BackRed      : 0
% 1.81/1.28  
% 1.81/1.28  #Partial instantiations: 0
% 1.81/1.28  #Strategies tried      : 1
% 1.81/1.28  
% 1.81/1.28  Timing (in seconds)
% 1.81/1.28  ----------------------
% 1.81/1.28  Preprocessing        : 0.28
% 1.81/1.28  Parsing              : 0.15
% 1.81/1.28  CNF conversion       : 0.02
% 1.81/1.28  Main loop            : 0.15
% 1.81/1.28  Inferencing          : 0.06
% 1.81/1.28  Reduction            : 0.05
% 1.81/1.28  Demodulation         : 0.04
% 1.81/1.29  BG Simplification    : 0.01
% 1.81/1.29  Subsumption          : 0.02
% 1.81/1.29  Abstraction          : 0.01
% 1.81/1.29  MUC search           : 0.00
% 1.81/1.29  Cooper               : 0.00
% 1.81/1.29  Total                : 0.46
% 1.81/1.29  Index Insertion      : 0.00
% 1.81/1.29  Index Deletion       : 0.00
% 1.81/1.29  Index Matching       : 0.00
% 1.81/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
