%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:41 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 (  88 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B) )
       => ! [C] :
            ( r2_hidden(C,k1_relat_1(B))
           => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k2_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).

tff(c_18,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,(
    ! [B_26,A_27] :
      ( r2_hidden(k1_funct_1(B_26,A_27),k2_relat_1(B_26))
      | ~ r2_hidden(A_27,k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    ! [A_15,B_16] :
      ( k8_relat_1(A_15,B_16) = B_16
      | ~ r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_17,B_18] :
      ( k8_relat_1(A_17,B_18) = B_18
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_4,c_31])).

tff(c_39,plain,
    ( k8_relat_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_36])).

tff(c_42,plain,(
    k8_relat_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_39])).

tff(c_47,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(A_19,B_20)
      | ~ r2_hidden(A_19,k2_relat_1(k8_relat_1(B_20,C_21)))
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ! [A_19] :
      ( r2_hidden(A_19,'#skF_1')
      | ~ r2_hidden(A_19,k2_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_47])).

tff(c_52,plain,(
    ! [A_19] :
      ( r2_hidden(A_19,'#skF_1')
      | ~ r2_hidden(A_19,k2_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_50])).

tff(c_68,plain,(
    ! [A_27] :
      ( r2_hidden(k1_funct_1('#skF_2',A_27),'#skF_1')
      | ~ r2_hidden(A_27,k1_relat_1('#skF_2'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_52])).

tff(c_78,plain,(
    ! [A_28] :
      ( r2_hidden(k1_funct_1('#skF_2',A_28),'#skF_1')
      | ~ r2_hidden(A_28,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_68])).

tff(c_16,plain,(
    ~ r2_hidden(k1_funct_1('#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_81,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_16])).

tff(c_85,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.22  
% 1.83/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.22  %$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.83/1.22  
% 1.83/1.22  %Foreground sorts:
% 1.83/1.22  
% 1.83/1.22  
% 1.83/1.22  %Background operators:
% 1.83/1.22  
% 1.83/1.22  
% 1.83/1.22  %Foreground operators:
% 1.83/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.83/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.83/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.83/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.83/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.22  
% 1.90/1.23  tff(f_65, negated_conjecture, ~(![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 1.90/1.23  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 1.90/1.23  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.90/1.23  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 1.90/1.23  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k2_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, B) & r2_hidden(A, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_relat_1)).
% 1.90/1.23  tff(c_18, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.90/1.23  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.90/1.23  tff(c_20, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.90/1.23  tff(c_60, plain, (![B_26, A_27]: (r2_hidden(k1_funct_1(B_26, A_27), k2_relat_1(B_26)) | ~r2_hidden(A_27, k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.23  tff(c_22, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.90/1.23  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.23  tff(c_31, plain, (![A_15, B_16]: (k8_relat_1(A_15, B_16)=B_16 | ~r1_tarski(k2_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.90/1.23  tff(c_36, plain, (![A_17, B_18]: (k8_relat_1(A_17, B_18)=B_18 | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_4, c_31])).
% 1.90/1.23  tff(c_39, plain, (k8_relat_1('#skF_1', '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_36])).
% 1.90/1.23  tff(c_42, plain, (k8_relat_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_39])).
% 1.90/1.23  tff(c_47, plain, (![A_19, B_20, C_21]: (r2_hidden(A_19, B_20) | ~r2_hidden(A_19, k2_relat_1(k8_relat_1(B_20, C_21))) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.23  tff(c_50, plain, (![A_19]: (r2_hidden(A_19, '#skF_1') | ~r2_hidden(A_19, k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_47])).
% 1.90/1.23  tff(c_52, plain, (![A_19]: (r2_hidden(A_19, '#skF_1') | ~r2_hidden(A_19, k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_50])).
% 1.90/1.23  tff(c_68, plain, (![A_27]: (r2_hidden(k1_funct_1('#skF_2', A_27), '#skF_1') | ~r2_hidden(A_27, k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_52])).
% 1.90/1.23  tff(c_78, plain, (![A_28]: (r2_hidden(k1_funct_1('#skF_2', A_28), '#skF_1') | ~r2_hidden(A_28, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_68])).
% 1.90/1.23  tff(c_16, plain, (~r2_hidden(k1_funct_1('#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.90/1.23  tff(c_81, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_78, c_16])).
% 1.90/1.23  tff(c_85, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_81])).
% 1.90/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.23  
% 1.90/1.23  Inference rules
% 1.90/1.23  ----------------------
% 1.90/1.23  #Ref     : 0
% 1.90/1.23  #Sup     : 11
% 1.90/1.23  #Fact    : 0
% 1.90/1.23  #Define  : 0
% 1.90/1.23  #Split   : 0
% 1.90/1.23  #Chain   : 0
% 1.90/1.23  #Close   : 0
% 1.90/1.23  
% 1.90/1.23  Ordering : KBO
% 1.90/1.23  
% 1.90/1.23  Simplification rules
% 1.90/1.23  ----------------------
% 1.90/1.23  #Subsume      : 0
% 1.90/1.23  #Demod        : 6
% 1.90/1.23  #Tautology    : 4
% 1.90/1.23  #SimpNegUnit  : 0
% 1.90/1.23  #BackRed      : 0
% 1.90/1.23  
% 1.90/1.23  #Partial instantiations: 0
% 1.90/1.23  #Strategies tried      : 1
% 1.90/1.23  
% 1.90/1.23  Timing (in seconds)
% 1.90/1.23  ----------------------
% 1.90/1.24  Preprocessing        : 0.29
% 1.90/1.24  Parsing              : 0.16
% 1.90/1.24  CNF conversion       : 0.02
% 1.90/1.24  Main loop            : 0.11
% 1.90/1.24  Inferencing          : 0.05
% 1.90/1.24  Reduction            : 0.03
% 1.90/1.24  Demodulation         : 0.02
% 1.90/1.24  BG Simplification    : 0.01
% 1.90/1.24  Subsumption          : 0.02
% 1.90/1.24  Abstraction          : 0.00
% 1.90/1.24  MUC search           : 0.00
% 1.90/1.24  Cooper               : 0.00
% 1.90/1.24  Total                : 0.43
% 1.90/1.24  Index Insertion      : 0.00
% 1.90/1.24  Index Deletion       : 0.00
% 1.90/1.24  Index Matching       : 0.00
% 1.90/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
