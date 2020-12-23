%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:03 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  45 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_172,plain,(
    ! [B_48,A_49] :
      ( k3_xboole_0(k1_relat_1(B_48),A_49) = k1_relat_1(k7_relat_1(B_48,A_49))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_195,plain,(
    ! [A_29,A_49] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_29),A_49)) = k3_xboole_0(A_29,A_49)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_172])).

tff(c_199,plain,(
    ! [A_29,A_49] : k1_relat_1(k7_relat_1(k6_relat_1(A_29),A_49)) = k3_xboole_0(A_29,A_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_195])).

tff(c_383,plain,(
    ! [A_65,B_66] :
      ( k7_relat_1(A_65,k1_relat_1(k7_relat_1(B_66,k1_relat_1(A_65)))) = k7_relat_1(A_65,k1_relat_1(B_66))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_418,plain,(
    ! [A_65,A_29] :
      ( k7_relat_1(A_65,k3_xboole_0(A_29,k1_relat_1(A_65))) = k7_relat_1(A_65,k1_relat_1(k6_relat_1(A_29)))
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_383])).

tff(c_439,plain,(
    ! [A_73,A_74] :
      ( k7_relat_1(A_73,k3_xboole_0(A_74,k1_relat_1(A_73))) = k7_relat_1(A_73,A_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20,c_418])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_81,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [B_41,A_42] : k1_setfam_1(k2_tarski(B_41,A_42)) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_81])).

tff(c_14,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_14])).

tff(c_26,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_161,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_26])).

tff(c_449,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_161])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:58:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.26  
% 2.22/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.26  %$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.22/1.26  
% 2.22/1.26  %Foreground sorts:
% 2.22/1.26  
% 2.22/1.26  
% 2.22/1.26  %Background operators:
% 2.22/1.26  
% 2.22/1.26  
% 2.22/1.26  %Foreground operators:
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.22/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.22/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.22/1.26  
% 2.33/1.27  tff(f_61, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 2.33/1.27  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.33/1.27  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.33/1.27  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.33/1.27  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 2.33/1.27  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.33/1.27  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.33/1.27  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.33/1.27  tff(c_16, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.27  tff(c_20, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.27  tff(c_172, plain, (![B_48, A_49]: (k3_xboole_0(k1_relat_1(B_48), A_49)=k1_relat_1(k7_relat_1(B_48, A_49)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.33/1.27  tff(c_195, plain, (![A_29, A_49]: (k1_relat_1(k7_relat_1(k6_relat_1(A_29), A_49))=k3_xboole_0(A_29, A_49) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_172])).
% 2.33/1.27  tff(c_199, plain, (![A_29, A_49]: (k1_relat_1(k7_relat_1(k6_relat_1(A_29), A_49))=k3_xboole_0(A_29, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_195])).
% 2.33/1.27  tff(c_383, plain, (![A_65, B_66]: (k7_relat_1(A_65, k1_relat_1(k7_relat_1(B_66, k1_relat_1(A_65))))=k7_relat_1(A_65, k1_relat_1(B_66)) | ~v1_relat_1(B_66) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.33/1.27  tff(c_418, plain, (![A_65, A_29]: (k7_relat_1(A_65, k3_xboole_0(A_29, k1_relat_1(A_65)))=k7_relat_1(A_65, k1_relat_1(k6_relat_1(A_29))) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(A_65))), inference(superposition, [status(thm), theory('equality')], [c_199, c_383])).
% 2.33/1.27  tff(c_439, plain, (![A_73, A_74]: (k7_relat_1(A_73, k3_xboole_0(A_74, k1_relat_1(A_73)))=k7_relat_1(A_73, A_74) | ~v1_relat_1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20, c_418])).
% 2.33/1.27  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.33/1.27  tff(c_81, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.27  tff(c_105, plain, (![B_41, A_42]: (k1_setfam_1(k2_tarski(B_41, A_42))=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_2, c_81])).
% 2.33/1.27  tff(c_14, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.27  tff(c_111, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_105, c_14])).
% 2.33/1.27  tff(c_26, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.33/1.27  tff(c_161, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_26])).
% 2.33/1.27  tff(c_449, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_439, c_161])).
% 2.33/1.27  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_449])).
% 2.33/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.27  
% 2.33/1.27  Inference rules
% 2.33/1.27  ----------------------
% 2.33/1.27  #Ref     : 0
% 2.33/1.27  #Sup     : 113
% 2.33/1.27  #Fact    : 0
% 2.33/1.27  #Define  : 0
% 2.33/1.27  #Split   : 0
% 2.33/1.27  #Chain   : 0
% 2.33/1.27  #Close   : 0
% 2.33/1.27  
% 2.33/1.27  Ordering : KBO
% 2.33/1.27  
% 2.33/1.27  Simplification rules
% 2.33/1.27  ----------------------
% 2.33/1.27  #Subsume      : 16
% 2.33/1.27  #Demod        : 30
% 2.33/1.27  #Tautology    : 54
% 2.33/1.27  #SimpNegUnit  : 0
% 2.33/1.27  #BackRed      : 0
% 2.33/1.27  
% 2.33/1.27  #Partial instantiations: 0
% 2.33/1.27  #Strategies tried      : 1
% 2.33/1.27  
% 2.33/1.27  Timing (in seconds)
% 2.33/1.27  ----------------------
% 2.33/1.28  Preprocessing        : 0.30
% 2.33/1.28  Parsing              : 0.16
% 2.33/1.28  CNF conversion       : 0.02
% 2.33/1.28  Main loop            : 0.22
% 2.33/1.28  Inferencing          : 0.09
% 2.33/1.28  Reduction            : 0.08
% 2.33/1.28  Demodulation         : 0.06
% 2.33/1.28  BG Simplification    : 0.02
% 2.33/1.28  Subsumption          : 0.03
% 2.33/1.28  Abstraction          : 0.02
% 2.33/1.28  MUC search           : 0.00
% 2.33/1.28  Cooper               : 0.00
% 2.33/1.28  Total                : 0.55
% 2.33/1.28  Index Insertion      : 0.00
% 2.33/1.28  Index Deletion       : 0.00
% 2.33/1.28  Index Matching       : 0.00
% 2.33/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
