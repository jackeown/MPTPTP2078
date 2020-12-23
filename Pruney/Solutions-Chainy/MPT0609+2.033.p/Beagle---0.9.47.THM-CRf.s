%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:35 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  58 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_20,A_19)),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_21] :
      ( k7_relat_1(A_21,k1_relat_1(A_21)) = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_111,plain,(
    ! [C_41,B_42,A_43] :
      ( k7_relat_1(k7_relat_1(C_41,B_42),A_43) = k7_relat_1(C_41,A_43)
      | ~ r1_tarski(A_43,B_42)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_162,plain,(
    ! [C_45,B_46] :
      ( k7_relat_1(C_45,k1_relat_1(k7_relat_1(C_45,B_46))) = k7_relat_1(C_45,B_46)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_45,B_46)),B_46)
      | ~ v1_relat_1(C_45)
      | ~ v1_relat_1(k7_relat_1(C_45,B_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_111])).

tff(c_170,plain,(
    ! [B_47,A_48] :
      ( k7_relat_1(B_47,k1_relat_1(k7_relat_1(B_47,A_48))) = k7_relat_1(B_47,A_48)
      | ~ v1_relat_1(k7_relat_1(B_47,A_48))
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_18,c_162])).

tff(c_8,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k6_subset_1(B_18,k7_relat_1(B_18,A_17))) = k6_subset_1(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_25,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k4_xboole_0(B_18,k7_relat_1(B_18,A_17))) = k4_xboole_0(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_16])).

tff(c_272,plain,(
    ! [B_60,A_61] :
      ( k4_xboole_0(k1_relat_1(B_60),k1_relat_1(k7_relat_1(B_60,A_61))) = k1_relat_1(k4_xboole_0(B_60,k7_relat_1(B_60,A_61)))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(k7_relat_1(B_60,A_61))
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_25])).

tff(c_22,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_22])).

tff(c_278,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_26])).

tff(c_297,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_278])).

tff(c_301,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_297])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.25  
% 2.15/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.26  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.15/1.26  
% 2.15/1.26  %Foreground sorts:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Background operators:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Foreground operators:
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.15/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.26  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.15/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.15/1.26  
% 2.15/1.27  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 2.15/1.27  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.15/1.27  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.15/1.27  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.15/1.27  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 2.15/1.27  tff(f_33, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.15/1.27  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 2.15/1.27  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.27  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.27  tff(c_18, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(k7_relat_1(B_20, A_19)), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.27  tff(c_20, plain, (![A_21]: (k7_relat_1(A_21, k1_relat_1(A_21))=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.15/1.27  tff(c_111, plain, (![C_41, B_42, A_43]: (k7_relat_1(k7_relat_1(C_41, B_42), A_43)=k7_relat_1(C_41, A_43) | ~r1_tarski(A_43, B_42) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.27  tff(c_162, plain, (![C_45, B_46]: (k7_relat_1(C_45, k1_relat_1(k7_relat_1(C_45, B_46)))=k7_relat_1(C_45, B_46) | ~r1_tarski(k1_relat_1(k7_relat_1(C_45, B_46)), B_46) | ~v1_relat_1(C_45) | ~v1_relat_1(k7_relat_1(C_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_111])).
% 2.15/1.27  tff(c_170, plain, (![B_47, A_48]: (k7_relat_1(B_47, k1_relat_1(k7_relat_1(B_47, A_48)))=k7_relat_1(B_47, A_48) | ~v1_relat_1(k7_relat_1(B_47, A_48)) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_18, c_162])).
% 2.15/1.27  tff(c_8, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.15/1.27  tff(c_16, plain, (![B_18, A_17]: (k1_relat_1(k6_subset_1(B_18, k7_relat_1(B_18, A_17)))=k6_subset_1(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.27  tff(c_25, plain, (![B_18, A_17]: (k1_relat_1(k4_xboole_0(B_18, k7_relat_1(B_18, A_17)))=k4_xboole_0(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_16])).
% 2.15/1.27  tff(c_272, plain, (![B_60, A_61]: (k4_xboole_0(k1_relat_1(B_60), k1_relat_1(k7_relat_1(B_60, A_61)))=k1_relat_1(k4_xboole_0(B_60, k7_relat_1(B_60, A_61))) | ~v1_relat_1(B_60) | ~v1_relat_1(k7_relat_1(B_60, A_61)) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_170, c_25])).
% 2.15/1.27  tff(c_22, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.27  tff(c_26, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_22])).
% 2.15/1.27  tff(c_278, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_272, c_26])).
% 2.15/1.27  tff(c_297, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_278])).
% 2.15/1.27  tff(c_301, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_297])).
% 2.15/1.27  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_301])).
% 2.15/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.27  
% 2.15/1.27  Inference rules
% 2.15/1.27  ----------------------
% 2.15/1.27  #Ref     : 0
% 2.15/1.27  #Sup     : 75
% 2.15/1.27  #Fact    : 0
% 2.15/1.27  #Define  : 0
% 2.15/1.27  #Split   : 0
% 2.15/1.27  #Chain   : 0
% 2.15/1.27  #Close   : 0
% 2.15/1.27  
% 2.15/1.27  Ordering : KBO
% 2.15/1.27  
% 2.15/1.27  Simplification rules
% 2.15/1.27  ----------------------
% 2.15/1.27  #Subsume      : 11
% 2.15/1.27  #Demod        : 6
% 2.15/1.27  #Tautology    : 29
% 2.15/1.27  #SimpNegUnit  : 0
% 2.15/1.27  #BackRed      : 0
% 2.15/1.27  
% 2.15/1.27  #Partial instantiations: 0
% 2.15/1.27  #Strategies tried      : 1
% 2.15/1.27  
% 2.15/1.27  Timing (in seconds)
% 2.15/1.27  ----------------------
% 2.15/1.27  Preprocessing        : 0.29
% 2.15/1.27  Parsing              : 0.16
% 2.15/1.27  CNF conversion       : 0.02
% 2.15/1.27  Main loop            : 0.22
% 2.15/1.27  Inferencing          : 0.09
% 2.15/1.27  Reduction            : 0.06
% 2.15/1.27  Demodulation         : 0.04
% 2.15/1.27  BG Simplification    : 0.02
% 2.15/1.27  Subsumption          : 0.04
% 2.15/1.27  Abstraction          : 0.02
% 2.15/1.27  MUC search           : 0.00
% 2.15/1.27  Cooper               : 0.00
% 2.15/1.27  Total                : 0.53
% 2.15/1.27  Index Insertion      : 0.00
% 2.15/1.27  Index Deletion       : 0.00
% 2.15/1.27  Index Matching       : 0.00
% 2.15/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
