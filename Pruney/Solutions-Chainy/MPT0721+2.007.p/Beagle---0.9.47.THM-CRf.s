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
% DateTime   : Thu Dec  3 10:05:53 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  77 expanded)
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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v5_relat_1(C,A)
          & v1_funct_1(C) )
       => ( r2_hidden(B,k1_relat_1(C))
         => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_16,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_3','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [A_16,B_17] :
      ( k8_relat_1(A_16,B_17) = B_17
      | ~ r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41,plain,(
    ! [A_18,B_19] :
      ( k8_relat_1(A_18,B_19) = B_19
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_44,plain,
    ( k8_relat_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_41])).

tff(c_47,plain,(
    k8_relat_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_44])).

tff(c_58,plain,(
    ! [C_23,A_24,B_25] :
      ( r2_hidden(k1_funct_1(C_23,A_24),B_25)
      | ~ r2_hidden(A_24,k1_relat_1(k8_relat_1(B_25,C_23)))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_61,plain,(
    ! [A_24] :
      ( r2_hidden(k1_funct_1('#skF_3',A_24),'#skF_1')
      | ~ r2_hidden(A_24,k1_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_58])).

tff(c_64,plain,(
    ! [A_26] :
      ( r2_hidden(k1_funct_1('#skF_3',A_26),'#skF_1')
      | ~ r2_hidden(A_26,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_61])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_30] :
      ( m1_subset_1(k1_funct_1('#skF_3',A_30),'#skF_1')
      | ~ r2_hidden(A_30,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_64,c_2])).

tff(c_90,plain,(
    m1_subset_1(k1_funct_1('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_87])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n011.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 10:53:57 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.14  %$ v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.67/1.14  
% 1.67/1.14  %Foreground sorts:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Background operators:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Foreground operators:
% 1.67/1.14  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.67/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.67/1.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.14  
% 1.67/1.15  tff(f_62, negated_conjecture, ~(![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 1.67/1.15  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.67/1.15  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.67/1.15  tff(f_51, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_funct_1)).
% 1.67/1.15  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 1.67/1.15  tff(c_16, plain, (~m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.67/1.15  tff(c_18, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.67/1.15  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.67/1.15  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.67/1.15  tff(c_22, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.67/1.15  tff(c_6, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.15  tff(c_36, plain, (![A_16, B_17]: (k8_relat_1(A_16, B_17)=B_17 | ~r1_tarski(k2_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.15  tff(c_41, plain, (![A_18, B_19]: (k8_relat_1(A_18, B_19)=B_19 | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_6, c_36])).
% 1.67/1.15  tff(c_44, plain, (k8_relat_1('#skF_1', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_41])).
% 1.67/1.15  tff(c_47, plain, (k8_relat_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_44])).
% 1.67/1.15  tff(c_58, plain, (![C_23, A_24, B_25]: (r2_hidden(k1_funct_1(C_23, A_24), B_25) | ~r2_hidden(A_24, k1_relat_1(k8_relat_1(B_25, C_23))) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.67/1.15  tff(c_61, plain, (![A_24]: (r2_hidden(k1_funct_1('#skF_3', A_24), '#skF_1') | ~r2_hidden(A_24, k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_47, c_58])).
% 1.67/1.15  tff(c_64, plain, (![A_26]: (r2_hidden(k1_funct_1('#skF_3', A_26), '#skF_1') | ~r2_hidden(A_26, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_61])).
% 1.67/1.15  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.15  tff(c_87, plain, (![A_30]: (m1_subset_1(k1_funct_1('#skF_3', A_30), '#skF_1') | ~r2_hidden(A_30, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_64, c_2])).
% 1.67/1.15  tff(c_90, plain, (m1_subset_1(k1_funct_1('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_18, c_87])).
% 1.67/1.15  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_90])).
% 1.67/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.15  
% 1.67/1.15  Inference rules
% 1.67/1.15  ----------------------
% 1.67/1.15  #Ref     : 0
% 1.67/1.15  #Sup     : 14
% 1.67/1.15  #Fact    : 0
% 1.67/1.15  #Define  : 0
% 1.67/1.15  #Split   : 0
% 1.67/1.15  #Chain   : 0
% 1.67/1.15  #Close   : 0
% 1.67/1.15  
% 1.67/1.15  Ordering : KBO
% 1.67/1.15  
% 1.67/1.15  Simplification rules
% 1.67/1.15  ----------------------
% 1.67/1.15  #Subsume      : 0
% 1.67/1.15  #Demod        : 7
% 1.67/1.15  #Tautology    : 7
% 1.67/1.15  #SimpNegUnit  : 1
% 1.67/1.15  #BackRed      : 0
% 1.67/1.15  
% 1.67/1.15  #Partial instantiations: 0
% 1.67/1.15  #Strategies tried      : 1
% 1.67/1.15  
% 1.67/1.15  Timing (in seconds)
% 1.67/1.15  ----------------------
% 1.67/1.15  Preprocessing        : 0.28
% 1.67/1.16  Parsing              : 0.15
% 1.67/1.16  CNF conversion       : 0.02
% 1.67/1.16  Main loop            : 0.13
% 1.67/1.16  Inferencing          : 0.06
% 1.67/1.16  Reduction            : 0.04
% 1.85/1.16  Demodulation         : 0.03
% 1.85/1.16  BG Simplification    : 0.01
% 1.85/1.16  Subsumption          : 0.02
% 1.85/1.16  Abstraction          : 0.01
% 1.85/1.16  MUC search           : 0.00
% 1.85/1.16  Cooper               : 0.00
% 1.85/1.16  Total                : 0.44
% 1.85/1.16  Index Insertion      : 0.00
% 1.85/1.16  Index Deletion       : 0.00
% 1.85/1.16  Index Matching       : 0.00
% 1.85/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
