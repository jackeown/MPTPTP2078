%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:54 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
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
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k7_relat_1(B_17,A_16),B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

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
    ! [A_16] :
      ( r1_tarski(k7_relat_1('#skF_3',A_16),'#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_47])).

tff(c_54,plain,(
    ! [A_16] : r1_tarski(k7_relat_1('#skF_3',A_16),'#skF_4') ),
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
    ! [A_16] :
      ( v1_relat_1(k7_relat_1('#skF_3',A_16))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_63])).

tff(c_82,plain,(
    ! [A_16] : v1_relat_1(k7_relat_1('#skF_3',A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_69])).

tff(c_10,plain,(
    ! [C_11,A_9,B_10] :
      ( k7_relat_1(k7_relat_1(C_11,A_9),B_10) = k7_relat_1(C_11,A_9)
      | ~ r1_tarski(A_9,B_10)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_164,plain,(
    ! [B_49,A_50,C_51] :
      ( r1_tarski(k7_relat_1(B_49,A_50),k7_relat_1(C_51,A_50))
      | ~ r1_tarski(B_49,C_51)
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1465,plain,(
    ! [C_140,A_141,C_142,B_143] :
      ( r1_tarski(k7_relat_1(C_140,A_141),k7_relat_1(C_142,B_143))
      | ~ r1_tarski(k7_relat_1(C_140,A_141),C_142)
      | ~ v1_relat_1(C_142)
      | ~ v1_relat_1(k7_relat_1(C_140,A_141))
      | ~ r1_tarski(A_141,B_143)
      | ~ v1_relat_1(C_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_164])).

tff(c_16,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1514,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1465,c_16])).

tff(c_1564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_82,c_22,c_54,c_1514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/2.02  
% 4.68/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/2.02  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.68/2.02  
% 4.68/2.02  %Foreground sorts:
% 4.68/2.02  
% 4.68/2.02  
% 4.68/2.02  %Background operators:
% 4.68/2.02  
% 4.68/2.02  
% 4.68/2.02  %Foreground operators:
% 4.68/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/2.02  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.68/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/2.02  tff('#skF_2', type, '#skF_2': $i).
% 4.68/2.02  tff('#skF_3', type, '#skF_3': $i).
% 4.68/2.02  tff('#skF_1', type, '#skF_1': $i).
% 4.68/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.68/2.02  tff('#skF_4', type, '#skF_4': $i).
% 4.68/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/2.02  
% 4.68/2.03  tff(f_73, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 4.68/2.03  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 4.68/2.03  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.68/2.03  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.68/2.03  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.68/2.03  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 4.68/2.03  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 4.68/2.03  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.68/2.03  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.68/2.03  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.68/2.03  tff(c_14, plain, (![B_17, A_16]: (r1_tarski(k7_relat_1(B_17, A_16), B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.68/2.03  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.68/2.03  tff(c_37, plain, (![A_27, C_28, B_29]: (r1_tarski(A_27, C_28) | ~r1_tarski(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.68/2.03  tff(c_47, plain, (![A_30]: (r1_tarski(A_30, '#skF_4') | ~r1_tarski(A_30, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_37])).
% 4.68/2.03  tff(c_51, plain, (![A_16]: (r1_tarski(k7_relat_1('#skF_3', A_16), '#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_47])).
% 4.68/2.03  tff(c_54, plain, (![A_16]: (r1_tarski(k7_relat_1('#skF_3', A_16), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_51])).
% 4.68/2.03  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.68/2.03  tff(c_32, plain, (![B_25, A_26]: (v1_relat_1(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.68/2.03  tff(c_63, plain, (![A_33, B_34]: (v1_relat_1(A_33) | ~v1_relat_1(B_34) | ~r1_tarski(A_33, B_34))), inference(resolution, [status(thm)], [c_6, c_32])).
% 4.68/2.03  tff(c_69, plain, (![A_16]: (v1_relat_1(k7_relat_1('#skF_3', A_16)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_63])).
% 4.68/2.03  tff(c_82, plain, (![A_16]: (v1_relat_1(k7_relat_1('#skF_3', A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_69])).
% 4.68/2.03  tff(c_10, plain, (![C_11, A_9, B_10]: (k7_relat_1(k7_relat_1(C_11, A_9), B_10)=k7_relat_1(C_11, A_9) | ~r1_tarski(A_9, B_10) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.68/2.03  tff(c_164, plain, (![B_49, A_50, C_51]: (r1_tarski(k7_relat_1(B_49, A_50), k7_relat_1(C_51, A_50)) | ~r1_tarski(B_49, C_51) | ~v1_relat_1(C_51) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.68/2.03  tff(c_1465, plain, (![C_140, A_141, C_142, B_143]: (r1_tarski(k7_relat_1(C_140, A_141), k7_relat_1(C_142, B_143)) | ~r1_tarski(k7_relat_1(C_140, A_141), C_142) | ~v1_relat_1(C_142) | ~v1_relat_1(k7_relat_1(C_140, A_141)) | ~r1_tarski(A_141, B_143) | ~v1_relat_1(C_140))), inference(superposition, [status(thm), theory('equality')], [c_10, c_164])).
% 4.68/2.03  tff(c_16, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.68/2.03  tff(c_1514, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1465, c_16])).
% 4.68/2.03  tff(c_1564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_82, c_22, c_54, c_1514])).
% 4.68/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/2.03  
% 4.68/2.03  Inference rules
% 4.68/2.03  ----------------------
% 4.68/2.03  #Ref     : 0
% 4.68/2.03  #Sup     : 335
% 4.68/2.03  #Fact    : 0
% 4.68/2.03  #Define  : 0
% 4.68/2.03  #Split   : 5
% 4.68/2.03  #Chain   : 0
% 4.68/2.03  #Close   : 0
% 4.68/2.03  
% 4.68/2.03  Ordering : KBO
% 4.68/2.03  
% 4.68/2.03  Simplification rules
% 4.68/2.03  ----------------------
% 4.68/2.03  #Subsume      : 79
% 4.68/2.03  #Demod        : 251
% 4.68/2.03  #Tautology    : 90
% 4.68/2.03  #SimpNegUnit  : 0
% 4.68/2.03  #BackRed      : 0
% 4.68/2.03  
% 4.68/2.03  #Partial instantiations: 0
% 4.68/2.03  #Strategies tried      : 1
% 4.68/2.03  
% 4.68/2.03  Timing (in seconds)
% 4.68/2.03  ----------------------
% 4.68/2.03  Preprocessing        : 0.44
% 4.68/2.03  Parsing              : 0.25
% 4.68/2.03  CNF conversion       : 0.03
% 4.68/2.03  Main loop            : 0.78
% 4.68/2.04  Inferencing          : 0.28
% 4.68/2.04  Reduction            : 0.23
% 4.68/2.04  Demodulation         : 0.17
% 4.68/2.04  BG Simplification    : 0.03
% 4.68/2.04  Subsumption          : 0.18
% 4.68/2.04  Abstraction          : 0.04
% 4.68/2.04  MUC search           : 0.00
% 4.68/2.04  Cooper               : 0.00
% 4.68/2.04  Total                : 1.25
% 4.68/2.04  Index Insertion      : 0.00
% 4.68/2.04  Index Deletion       : 0.00
% 4.68/2.04  Index Matching       : 0.00
% 4.68/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
