%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:17 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   39 (  58 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 126 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k8_relat_1(A_9,B_10),B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_37,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(A_27,C_28)
      | ~ r1_tarski(B_29,C_28)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_30] :
      ( r1_tarski(A_30,'#skF_4')
      | ~ r1_tarski(A_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_37])).

tff(c_51,plain,(
    ! [A_9] :
      ( r1_tarski(k8_relat_1(A_9,'#skF_3'),'#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_47])).

tff(c_54,plain,(
    ! [A_9] : r1_tarski(k8_relat_1(A_9,'#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_51])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [B_25,A_26] :
      ( v1_relat_1(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26))
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_63,plain,(
    ! [A_33,B_34] :
      ( v1_relat_1(A_33)
      | ~ v1_relat_1(B_34)
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_6,c_32])).

tff(c_69,plain,(
    ! [A_9] :
      ( v1_relat_1(k8_relat_1(A_9,'#skF_3'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_63])).

tff(c_82,plain,(
    ! [A_9] : v1_relat_1(k8_relat_1(A_9,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_69])).

tff(c_12,plain,(
    ! [B_12,A_11,C_13] :
      ( k8_relat_1(B_12,k8_relat_1(A_11,C_13)) = k8_relat_1(A_11,C_13)
      | ~ r1_tarski(A_11,B_12)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_164,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(k8_relat_1(A_49,B_50),k8_relat_1(A_49,C_51))
      | ~ r1_tarski(B_50,C_51)
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1465,plain,(
    ! [A_140,C_141,B_142,C_143] :
      ( r1_tarski(k8_relat_1(A_140,C_141),k8_relat_1(B_142,C_143))
      | ~ r1_tarski(k8_relat_1(A_140,C_141),C_143)
      | ~ v1_relat_1(C_143)
      | ~ v1_relat_1(k8_relat_1(A_140,C_141))
      | ~ r1_tarski(A_140,B_142)
      | ~ v1_relat_1(C_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_164])).

tff(c_16,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1514,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1465,c_16])).

tff(c_1564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_82,c_22,c_54,c_1514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.54  
% 3.70/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.54  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.70/1.54  
% 3.70/1.54  %Foreground sorts:
% 3.70/1.54  
% 3.70/1.54  
% 3.70/1.54  %Background operators:
% 3.70/1.54  
% 3.70/1.54  
% 3.70/1.54  %Foreground operators:
% 3.70/1.54  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.70/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.70/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.70/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.70/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.54  
% 3.70/1.55  tff(f_73, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 3.70/1.55  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 3.70/1.55  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.70/1.55  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.70/1.55  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.70/1.55  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 3.70/1.55  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_relat_1)).
% 3.70/1.55  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.70/1.55  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.70/1.55  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.70/1.55  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k8_relat_1(A_9, B_10), B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.70/1.55  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.70/1.55  tff(c_37, plain, (![A_27, C_28, B_29]: (r1_tarski(A_27, C_28) | ~r1_tarski(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.70/1.55  tff(c_47, plain, (![A_30]: (r1_tarski(A_30, '#skF_4') | ~r1_tarski(A_30, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_37])).
% 3.70/1.55  tff(c_51, plain, (![A_9]: (r1_tarski(k8_relat_1(A_9, '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_47])).
% 3.70/1.55  tff(c_54, plain, (![A_9]: (r1_tarski(k8_relat_1(A_9, '#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_51])).
% 3.70/1.55  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.70/1.55  tff(c_32, plain, (![B_25, A_26]: (v1_relat_1(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.70/1.55  tff(c_63, plain, (![A_33, B_34]: (v1_relat_1(A_33) | ~v1_relat_1(B_34) | ~r1_tarski(A_33, B_34))), inference(resolution, [status(thm)], [c_6, c_32])).
% 3.70/1.55  tff(c_69, plain, (![A_9]: (v1_relat_1(k8_relat_1(A_9, '#skF_3')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_63])).
% 3.70/1.55  tff(c_82, plain, (![A_9]: (v1_relat_1(k8_relat_1(A_9, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_69])).
% 3.70/1.55  tff(c_12, plain, (![B_12, A_11, C_13]: (k8_relat_1(B_12, k8_relat_1(A_11, C_13))=k8_relat_1(A_11, C_13) | ~r1_tarski(A_11, B_12) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.70/1.55  tff(c_164, plain, (![A_49, B_50, C_51]: (r1_tarski(k8_relat_1(A_49, B_50), k8_relat_1(A_49, C_51)) | ~r1_tarski(B_50, C_51) | ~v1_relat_1(C_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.70/1.55  tff(c_1465, plain, (![A_140, C_141, B_142, C_143]: (r1_tarski(k8_relat_1(A_140, C_141), k8_relat_1(B_142, C_143)) | ~r1_tarski(k8_relat_1(A_140, C_141), C_143) | ~v1_relat_1(C_143) | ~v1_relat_1(k8_relat_1(A_140, C_141)) | ~r1_tarski(A_140, B_142) | ~v1_relat_1(C_141))), inference(superposition, [status(thm), theory('equality')], [c_12, c_164])).
% 3.70/1.55  tff(c_16, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.70/1.55  tff(c_1514, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1465, c_16])).
% 3.70/1.55  tff(c_1564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_82, c_22, c_54, c_1514])).
% 3.70/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.55  
% 3.70/1.55  Inference rules
% 3.70/1.55  ----------------------
% 3.70/1.55  #Ref     : 0
% 3.70/1.55  #Sup     : 335
% 3.70/1.55  #Fact    : 0
% 3.70/1.55  #Define  : 0
% 3.70/1.55  #Split   : 5
% 3.70/1.55  #Chain   : 0
% 3.70/1.55  #Close   : 0
% 3.70/1.55  
% 3.70/1.55  Ordering : KBO
% 3.70/1.55  
% 3.70/1.55  Simplification rules
% 3.70/1.55  ----------------------
% 3.70/1.55  #Subsume      : 79
% 3.70/1.55  #Demod        : 251
% 3.70/1.55  #Tautology    : 90
% 3.70/1.55  #SimpNegUnit  : 0
% 3.70/1.55  #BackRed      : 0
% 3.70/1.55  
% 3.70/1.55  #Partial instantiations: 0
% 3.70/1.55  #Strategies tried      : 1
% 3.70/1.55  
% 3.70/1.55  Timing (in seconds)
% 3.70/1.55  ----------------------
% 3.70/1.55  Preprocessing        : 0.27
% 3.70/1.55  Parsing              : 0.15
% 3.70/1.55  CNF conversion       : 0.02
% 3.70/1.55  Main loop            : 0.52
% 3.70/1.55  Inferencing          : 0.19
% 3.70/1.55  Reduction            : 0.16
% 3.83/1.55  Demodulation         : 0.12
% 3.83/1.55  BG Simplification    : 0.02
% 3.83/1.55  Subsumption          : 0.12
% 3.83/1.55  Abstraction          : 0.03
% 3.83/1.55  MUC search           : 0.00
% 3.83/1.55  Cooper               : 0.00
% 3.83/1.55  Total                : 0.82
% 3.83/1.55  Index Insertion      : 0.00
% 3.83/1.55  Index Deletion       : 0.00
% 3.83/1.55  Index Matching       : 0.00
% 3.83/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
