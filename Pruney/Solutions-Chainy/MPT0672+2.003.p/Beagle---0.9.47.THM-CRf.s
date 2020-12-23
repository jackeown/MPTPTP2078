%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:21 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  85 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r1_tarski(A,B)
         => ( k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C)
            & k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_22])).

tff(c_668,plain,(
    ! [A_81,B_82,C_83] :
      ( k8_relat_1(k3_xboole_0(A_81,B_82),C_83) = k8_relat_1(A_81,k8_relat_1(B_82,C_83))
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_727,plain,(
    ! [C_88] :
      ( k8_relat_1('#skF_1',k8_relat_1('#skF_2',C_88)) = k8_relat_1('#skF_1',C_88)
      | ~ v1_relat_1(C_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_668])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_8,B_9)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(A_21,C_22)
      | ~ r1_tarski(B_23,C_22)
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_21] :
      ( r1_tarski(A_21,'#skF_2')
      | ~ r1_tarski(A_21,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_36])).

tff(c_69,plain,(
    ! [A_28,B_29] :
      ( k8_relat_1(A_28,B_29) = B_29
      | ~ r1_tarski(k2_relat_1(B_29),A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    ! [B_30] :
      ( k8_relat_1('#skF_2',B_30) = B_30
      | ~ v1_relat_1(B_30)
      | ~ r1_tarski(k2_relat_1(B_30),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_478,plain,(
    ! [B_70] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_70)) = k8_relat_1('#skF_1',B_70)
      | ~ v1_relat_1(k8_relat_1('#skF_1',B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_532,plain,(
    ! [B_75] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_75)) = k8_relat_1('#skF_1',B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_478])).

tff(c_14,plain,
    ( k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3')
    | k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_595,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_51])).

tff(c_618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_595])).

tff(c_619,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_739,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_619])).

tff(c_756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:08:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.40  
% 2.68/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.40  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.68/1.40  
% 2.68/1.40  %Foreground sorts:
% 2.68/1.40  
% 2.68/1.40  
% 2.68/1.40  %Background operators:
% 2.68/1.40  
% 2.68/1.40  
% 2.68/1.40  %Foreground operators:
% 2.68/1.40  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.68/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.68/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.40  
% 2.68/1.41  tff(f_64, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C)) & (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_funct_1)).
% 2.68/1.41  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.68/1.41  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 2.68/1.41  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.68/1.41  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.68/1.41  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.68/1.41  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.68/1.41  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.68/1.41  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.68/1.41  tff(c_22, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.41  tff(c_26, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_16, c_22])).
% 2.68/1.41  tff(c_668, plain, (![A_81, B_82, C_83]: (k8_relat_1(k3_xboole_0(A_81, B_82), C_83)=k8_relat_1(A_81, k8_relat_1(B_82, C_83)) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.68/1.41  tff(c_727, plain, (![C_88]: (k8_relat_1('#skF_1', k8_relat_1('#skF_2', C_88))=k8_relat_1('#skF_1', C_88) | ~v1_relat_1(C_88))), inference(superposition, [status(thm), theory('equality')], [c_26, c_668])).
% 2.68/1.41  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.41  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k2_relat_1(k8_relat_1(A_8, B_9)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.68/1.41  tff(c_36, plain, (![A_21, C_22, B_23]: (r1_tarski(A_21, C_22) | ~r1_tarski(B_23, C_22) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.68/1.41  tff(c_42, plain, (![A_21]: (r1_tarski(A_21, '#skF_2') | ~r1_tarski(A_21, '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_36])).
% 2.68/1.41  tff(c_69, plain, (![A_28, B_29]: (k8_relat_1(A_28, B_29)=B_29 | ~r1_tarski(k2_relat_1(B_29), A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.41  tff(c_79, plain, (![B_30]: (k8_relat_1('#skF_2', B_30)=B_30 | ~v1_relat_1(B_30) | ~r1_tarski(k2_relat_1(B_30), '#skF_1'))), inference(resolution, [status(thm)], [c_42, c_69])).
% 2.68/1.41  tff(c_478, plain, (![B_70]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_70))=k8_relat_1('#skF_1', B_70) | ~v1_relat_1(k8_relat_1('#skF_1', B_70)) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_8, c_79])).
% 2.68/1.41  tff(c_532, plain, (![B_75]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_75))=k8_relat_1('#skF_1', B_75) | ~v1_relat_1(B_75))), inference(resolution, [status(thm)], [c_6, c_478])).
% 2.68/1.41  tff(c_14, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3') | k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.68/1.41  tff(c_51, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_14])).
% 2.68/1.41  tff(c_595, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_532, c_51])).
% 2.68/1.41  tff(c_618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_595])).
% 2.68/1.41  tff(c_619, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_14])).
% 2.68/1.41  tff(c_739, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_727, c_619])).
% 2.68/1.41  tff(c_756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_739])).
% 2.68/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.41  
% 2.68/1.41  Inference rules
% 2.68/1.41  ----------------------
% 2.68/1.41  #Ref     : 0
% 2.68/1.41  #Sup     : 196
% 2.68/1.41  #Fact    : 0
% 2.68/1.41  #Define  : 0
% 2.68/1.41  #Split   : 3
% 2.68/1.41  #Chain   : 0
% 2.68/1.41  #Close   : 0
% 2.68/1.41  
% 2.68/1.41  Ordering : KBO
% 2.68/1.41  
% 2.68/1.41  Simplification rules
% 2.68/1.41  ----------------------
% 2.68/1.41  #Subsume      : 43
% 2.68/1.41  #Demod        : 15
% 2.68/1.41  #Tautology    : 29
% 2.68/1.41  #SimpNegUnit  : 0
% 2.68/1.41  #BackRed      : 0
% 2.68/1.41  
% 2.68/1.41  #Partial instantiations: 0
% 2.68/1.41  #Strategies tried      : 1
% 2.68/1.41  
% 2.68/1.41  Timing (in seconds)
% 2.68/1.41  ----------------------
% 2.68/1.42  Preprocessing        : 0.27
% 2.68/1.42  Parsing              : 0.16
% 2.68/1.42  CNF conversion       : 0.02
% 2.68/1.42  Main loop            : 0.37
% 2.68/1.42  Inferencing          : 0.15
% 2.68/1.42  Reduction            : 0.08
% 2.68/1.42  Demodulation         : 0.06
% 2.68/1.42  BG Simplification    : 0.02
% 2.68/1.42  Subsumption          : 0.09
% 2.68/1.42  Abstraction          : 0.02
% 2.68/1.42  MUC search           : 0.00
% 2.68/1.42  Cooper               : 0.00
% 2.86/1.42  Total                : 0.67
% 2.86/1.42  Index Insertion      : 0.00
% 2.86/1.42  Index Deletion       : 0.00
% 2.86/1.42  Index Matching       : 0.00
% 2.86/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
