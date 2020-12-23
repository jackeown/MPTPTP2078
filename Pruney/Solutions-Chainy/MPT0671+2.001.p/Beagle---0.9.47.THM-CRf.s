%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:20 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   34 (  49 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  81 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k8_relat_1(A_6,B_7),B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [B_17,A_18] :
      ( v1_relat_1(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_31,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(A_19)
      | ~ v1_relat_1(B_20)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_4,c_26])).

tff(c_35,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_31])).

tff(c_37,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_relat_1(A_23),k1_relat_1(B_24))
      | ~ r1_tarski(A_23,B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_43,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_37,c_14])).

tff(c_47,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_43])).

tff(c_48,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_51,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_35,c_48])).

tff(c_55,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_51])).

tff(c_56,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_60,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:44:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.10  
% 1.71/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.10  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.71/1.10  
% 1.71/1.10  %Foreground sorts:
% 1.71/1.10  
% 1.71/1.10  
% 1.71/1.10  %Background operators:
% 1.71/1.10  
% 1.71/1.10  
% 1.71/1.10  %Foreground operators:
% 1.71/1.10  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.71/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.71/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.71/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.71/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.71/1.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.71/1.10  
% 1.71/1.11  tff(f_58, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k1_relat_1(k8_relat_1(A, B)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_funct_1)).
% 1.71/1.11  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 1.71/1.11  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.71/1.11  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.71/1.11  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.71/1.11  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.11  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k8_relat_1(A_6, B_7), B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.71/1.11  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.11  tff(c_26, plain, (![B_17, A_18]: (v1_relat_1(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_18)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.71/1.11  tff(c_31, plain, (![A_19, B_20]: (v1_relat_1(A_19) | ~v1_relat_1(B_20) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_4, c_26])).
% 1.71/1.11  tff(c_35, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_8, c_31])).
% 1.71/1.11  tff(c_37, plain, (![A_23, B_24]: (r1_tarski(k1_relat_1(A_23), k1_relat_1(B_24)) | ~r1_tarski(A_23, B_24) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.71/1.11  tff(c_14, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.11  tff(c_43, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_37, c_14])).
% 1.71/1.11  tff(c_47, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_43])).
% 1.71/1.11  tff(c_48, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_47])).
% 1.71/1.11  tff(c_51, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_35, c_48])).
% 1.71/1.11  tff(c_55, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_51])).
% 1.71/1.11  tff(c_56, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_47])).
% 1.71/1.11  tff(c_60, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_56])).
% 1.71/1.11  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_60])).
% 1.71/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.11  
% 1.71/1.11  Inference rules
% 1.71/1.11  ----------------------
% 1.71/1.11  #Ref     : 0
% 1.71/1.11  #Sup     : 7
% 1.71/1.11  #Fact    : 0
% 1.71/1.11  #Define  : 0
% 1.71/1.11  #Split   : 1
% 1.71/1.11  #Chain   : 0
% 1.71/1.11  #Close   : 0
% 1.71/1.11  
% 1.71/1.11  Ordering : KBO
% 1.71/1.11  
% 1.71/1.11  Simplification rules
% 1.71/1.11  ----------------------
% 1.71/1.11  #Subsume      : 0
% 1.71/1.11  #Demod        : 3
% 1.71/1.11  #Tautology    : 1
% 1.71/1.11  #SimpNegUnit  : 0
% 1.71/1.11  #BackRed      : 0
% 1.71/1.11  
% 1.71/1.11  #Partial instantiations: 0
% 1.71/1.11  #Strategies tried      : 1
% 1.71/1.11  
% 1.71/1.11  Timing (in seconds)
% 1.71/1.11  ----------------------
% 1.71/1.11  Preprocessing        : 0.26
% 1.71/1.11  Parsing              : 0.15
% 1.71/1.11  CNF conversion       : 0.02
% 1.71/1.11  Main loop            : 0.10
% 1.71/1.11  Inferencing          : 0.05
% 1.71/1.11  Reduction            : 0.02
% 1.71/1.11  Demodulation         : 0.02
% 1.71/1.11  BG Simplification    : 0.01
% 1.71/1.11  Subsumption          : 0.01
% 1.71/1.11  Abstraction          : 0.00
% 1.71/1.11  MUC search           : 0.00
% 1.71/1.11  Cooper               : 0.00
% 1.71/1.11  Total                : 0.38
% 1.71/1.11  Index Insertion      : 0.00
% 1.71/1.11  Index Deletion       : 0.00
% 1.71/1.11  Index Matching       : 0.00
% 1.71/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
