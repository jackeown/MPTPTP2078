%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:53 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 (  94 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v5_relat_1(C,A)
          & v1_funct_1(C) )
       => ( r2_hidden(B,k1_relat_1(C))
         => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k2_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_18,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_3','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_67,plain,(
    ! [B_29,A_30] :
      ( r2_hidden(k1_funct_1(B_29,A_30),k2_relat_1(B_29))
      | ~ r2_hidden(A_30,k1_relat_1(B_29))
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( k8_relat_1(A_18,B_19) = B_19
      | ~ r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43,plain,(
    ! [A_20,B_21] :
      ( k8_relat_1(A_20,B_21) = B_21
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_46,plain,
    ( k8_relat_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_43])).

tff(c_49,plain,(
    k8_relat_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_46])).

tff(c_54,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_hidden(A_22,B_23)
      | ~ r2_hidden(A_22,k2_relat_1(k8_relat_1(B_23,C_24)))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,(
    ! [A_22] :
      ( r2_hidden(A_22,'#skF_1')
      | ~ r2_hidden(A_22,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_54])).

tff(c_59,plain,(
    ! [A_22] :
      ( r2_hidden(A_22,'#skF_1')
      | ~ r2_hidden(A_22,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_57])).

tff(c_75,plain,(
    ! [A_30] :
      ( r2_hidden(k1_funct_1('#skF_3',A_30),'#skF_1')
      | ~ r2_hidden(A_30,k1_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_67,c_59])).

tff(c_89,plain,(
    ! [A_31] :
      ( r2_hidden(k1_funct_1('#skF_3',A_31),'#skF_1')
      | ~ r2_hidden(A_31,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_75])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_94,plain,(
    ! [A_32] :
      ( m1_subset_1(k1_funct_1('#skF_3',A_32),'#skF_1')
      | ~ r2_hidden(A_32,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_97,plain,(
    m1_subset_1(k1_funct_1('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_94])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.24  
% 1.68/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.24  %$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.68/1.24  
% 1.68/1.24  %Foreground sorts:
% 1.68/1.24  
% 1.68/1.24  
% 1.68/1.24  %Background operators:
% 1.68/1.24  
% 1.68/1.24  
% 1.68/1.24  %Foreground operators:
% 1.68/1.24  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.68/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.68/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.68/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.68/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.68/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.68/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.24  
% 1.82/1.25  tff(f_68, negated_conjecture, ~(![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 1.82/1.25  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.82/1.25  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.82/1.25  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.82/1.25  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k2_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, B) & r2_hidden(A, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_relat_1)).
% 1.82/1.25  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 1.82/1.25  tff(c_18, plain, (~m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.82/1.25  tff(c_20, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.82/1.25  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.82/1.25  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.82/1.25  tff(c_67, plain, (![B_29, A_30]: (r2_hidden(k1_funct_1(B_29, A_30), k2_relat_1(B_29)) | ~r2_hidden(A_30, k1_relat_1(B_29)) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.25  tff(c_24, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.82/1.25  tff(c_6, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.25  tff(c_38, plain, (![A_18, B_19]: (k8_relat_1(A_18, B_19)=B_19 | ~r1_tarski(k2_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.82/1.25  tff(c_43, plain, (![A_20, B_21]: (k8_relat_1(A_20, B_21)=B_21 | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_6, c_38])).
% 1.82/1.25  tff(c_46, plain, (k8_relat_1('#skF_1', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_43])).
% 1.82/1.25  tff(c_49, plain, (k8_relat_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_46])).
% 1.82/1.25  tff(c_54, plain, (![A_22, B_23, C_24]: (r2_hidden(A_22, B_23) | ~r2_hidden(A_22, k2_relat_1(k8_relat_1(B_23, C_24))) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.82/1.25  tff(c_57, plain, (![A_22]: (r2_hidden(A_22, '#skF_1') | ~r2_hidden(A_22, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_54])).
% 1.82/1.25  tff(c_59, plain, (![A_22]: (r2_hidden(A_22, '#skF_1') | ~r2_hidden(A_22, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_57])).
% 1.82/1.25  tff(c_75, plain, (![A_30]: (r2_hidden(k1_funct_1('#skF_3', A_30), '#skF_1') | ~r2_hidden(A_30, k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_67, c_59])).
% 1.82/1.25  tff(c_89, plain, (![A_31]: (r2_hidden(k1_funct_1('#skF_3', A_31), '#skF_1') | ~r2_hidden(A_31, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_75])).
% 1.82/1.25  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.25  tff(c_94, plain, (![A_32]: (m1_subset_1(k1_funct_1('#skF_3', A_32), '#skF_1') | ~r2_hidden(A_32, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_89, c_2])).
% 1.82/1.25  tff(c_97, plain, (m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_20, c_94])).
% 1.82/1.25  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_97])).
% 1.82/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.25  
% 1.82/1.25  Inference rules
% 1.82/1.25  ----------------------
% 1.82/1.25  #Ref     : 0
% 1.82/1.25  #Sup     : 14
% 1.82/1.25  #Fact    : 0
% 1.82/1.25  #Define  : 0
% 1.82/1.25  #Split   : 0
% 1.82/1.25  #Chain   : 0
% 1.82/1.25  #Close   : 0
% 1.82/1.25  
% 1.82/1.25  Ordering : KBO
% 1.82/1.25  
% 1.82/1.25  Simplification rules
% 1.82/1.25  ----------------------
% 1.82/1.25  #Subsume      : 0
% 1.82/1.25  #Demod        : 5
% 1.82/1.25  #Tautology    : 4
% 1.82/1.25  #SimpNegUnit  : 1
% 1.82/1.25  #BackRed      : 0
% 1.82/1.25  
% 1.82/1.25  #Partial instantiations: 0
% 1.82/1.25  #Strategies tried      : 1
% 1.82/1.25  
% 1.82/1.25  Timing (in seconds)
% 1.82/1.25  ----------------------
% 1.85/1.26  Preprocessing        : 0.27
% 1.85/1.26  Parsing              : 0.14
% 1.85/1.26  CNF conversion       : 0.02
% 1.85/1.26  Main loop            : 0.12
% 1.85/1.26  Inferencing          : 0.05
% 1.85/1.26  Reduction            : 0.03
% 1.85/1.26  Demodulation         : 0.02
% 1.85/1.26  BG Simplification    : 0.01
% 1.85/1.26  Subsumption          : 0.02
% 1.85/1.26  Abstraction          : 0.01
% 1.85/1.26  MUC search           : 0.00
% 1.85/1.26  Cooper               : 0.00
% 1.85/1.26  Total                : 0.42
% 1.85/1.26  Index Insertion      : 0.00
% 1.85/1.26  Index Deletion       : 0.00
% 1.85/1.26  Index Matching       : 0.00
% 1.85/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
