%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:41 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  71 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B) )
       => ! [C] :
            ( r2_hidden(C,k1_relat_1(B))
           => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

tff(c_16,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [A_13,B_14] :
      ( k8_relat_1(A_13,B_14) = B_14
      | ~ r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [A_15,B_16] :
      ( k8_relat_1(A_15,B_16) = B_16
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_4,c_29])).

tff(c_37,plain,
    ( k8_relat_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_34])).

tff(c_40,plain,(
    k8_relat_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_37])).

tff(c_51,plain,(
    ! [C_20,A_21,B_22] :
      ( r2_hidden(k1_funct_1(C_20,A_21),B_22)
      | ~ r2_hidden(A_21,k1_relat_1(k8_relat_1(B_22,C_20)))
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [A_21] :
      ( r2_hidden(k1_funct_1('#skF_2',A_21),'#skF_1')
      | ~ r2_hidden(A_21,k1_relat_1('#skF_2'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_51])).

tff(c_57,plain,(
    ! [A_23] :
      ( r2_hidden(k1_funct_1('#skF_2',A_23),'#skF_1')
      | ~ r2_hidden(A_23,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_54])).

tff(c_14,plain,(
    ~ r2_hidden(k1_funct_1('#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_57,c_14])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:09:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.20  
% 1.72/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.21  %$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.72/1.21  
% 1.72/1.21  %Foreground sorts:
% 1.72/1.21  
% 1.72/1.21  
% 1.72/1.21  %Background operators:
% 1.72/1.21  
% 1.72/1.21  
% 1.72/1.21  %Foreground operators:
% 1.72/1.21  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.72/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.72/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.72/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.72/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.72/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.72/1.21  
% 1.72/1.22  tff(f_59, negated_conjecture, ~(![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 1.72/1.22  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.72/1.22  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 1.72/1.22  tff(f_47, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 1.72/1.22  tff(c_16, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.72/1.22  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.72/1.22  tff(c_18, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.72/1.22  tff(c_20, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.72/1.22  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.22  tff(c_29, plain, (![A_13, B_14]: (k8_relat_1(A_13, B_14)=B_14 | ~r1_tarski(k2_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.72/1.22  tff(c_34, plain, (![A_15, B_16]: (k8_relat_1(A_15, B_16)=B_16 | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_4, c_29])).
% 1.72/1.22  tff(c_37, plain, (k8_relat_1('#skF_1', '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_34])).
% 1.72/1.22  tff(c_40, plain, (k8_relat_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_37])).
% 1.72/1.22  tff(c_51, plain, (![C_20, A_21, B_22]: (r2_hidden(k1_funct_1(C_20, A_21), B_22) | ~r2_hidden(A_21, k1_relat_1(k8_relat_1(B_22, C_20))) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.72/1.22  tff(c_54, plain, (![A_21]: (r2_hidden(k1_funct_1('#skF_2', A_21), '#skF_1') | ~r2_hidden(A_21, k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_51])).
% 1.72/1.22  tff(c_57, plain, (![A_23]: (r2_hidden(k1_funct_1('#skF_2', A_23), '#skF_1') | ~r2_hidden(A_23, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_54])).
% 1.72/1.22  tff(c_14, plain, (~r2_hidden(k1_funct_1('#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.72/1.22  tff(c_60, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_57, c_14])).
% 1.72/1.22  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_60])).
% 1.72/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.22  
% 1.72/1.22  Inference rules
% 1.72/1.22  ----------------------
% 1.72/1.22  #Ref     : 0
% 1.72/1.22  #Sup     : 8
% 1.72/1.22  #Fact    : 0
% 1.72/1.22  #Define  : 0
% 1.72/1.22  #Split   : 0
% 1.72/1.22  #Chain   : 0
% 1.72/1.22  #Close   : 0
% 1.72/1.22  
% 1.72/1.22  Ordering : KBO
% 1.72/1.22  
% 1.72/1.22  Simplification rules
% 1.72/1.22  ----------------------
% 1.72/1.22  #Subsume      : 0
% 1.72/1.22  #Demod        : 6
% 1.72/1.22  #Tautology    : 4
% 1.72/1.22  #SimpNegUnit  : 0
% 1.72/1.22  #BackRed      : 0
% 1.72/1.22  
% 1.72/1.22  #Partial instantiations: 0
% 1.72/1.22  #Strategies tried      : 1
% 1.72/1.22  
% 1.72/1.22  Timing (in seconds)
% 1.72/1.22  ----------------------
% 1.72/1.22  Preprocessing        : 0.29
% 1.72/1.22  Parsing              : 0.16
% 1.72/1.22  CNF conversion       : 0.02
% 1.72/1.22  Main loop            : 0.10
% 1.72/1.22  Inferencing          : 0.05
% 1.72/1.22  Reduction            : 0.03
% 1.72/1.22  Demodulation         : 0.02
% 1.72/1.22  BG Simplification    : 0.01
% 1.72/1.22  Subsumption          : 0.01
% 1.72/1.22  Abstraction          : 0.00
% 1.72/1.22  MUC search           : 0.00
% 1.72/1.22  Cooper               : 0.00
% 1.72/1.22  Total                : 0.42
% 1.72/1.22  Index Insertion      : 0.00
% 1.72/1.22  Index Deletion       : 0.00
% 1.72/1.22  Index Matching       : 0.00
% 1.72/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
