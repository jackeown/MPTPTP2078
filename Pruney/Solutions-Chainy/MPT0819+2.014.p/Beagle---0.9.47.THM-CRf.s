%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:59 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  61 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_54])).

tff(c_227,plain,(
    ! [A_35,C_36,B_37,D_38] :
      ( r1_tarski(k2_zfmisc_1(A_35,C_36),k2_zfmisc_1(B_37,D_38))
      | ~ r1_tarski(C_36,D_38)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_495,plain,(
    ! [A_50,C_51,B_52,D_53] :
      ( k2_xboole_0(k2_zfmisc_1(A_50,C_51),k2_zfmisc_1(B_52,D_53)) = k2_zfmisc_1(B_52,D_53)
      | ~ r1_tarski(C_51,D_53)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(resolution,[status(thm)],[c_227,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_108,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_tarski(A_22,k2_xboole_0(C_23,B_24))
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [A_22,A_1,B_2] :
      ( r1_tarski(A_22,k2_xboole_0(A_1,B_2))
      | ~ r1_tarski(A_22,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_108])).

tff(c_838,plain,(
    ! [D_74,A_70,C_72,A_73,B_71] :
      ( r1_tarski(A_70,k2_zfmisc_1(B_71,D_74))
      | ~ r1_tarski(A_70,k2_zfmisc_1(A_73,C_72))
      | ~ r1_tarski(C_72,D_74)
      | ~ r1_tarski(A_73,B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_126])).

tff(c_1413,plain,(
    ! [B_96,D_97] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(B_96,D_97))
      | ~ r1_tarski('#skF_3',D_97)
      | ~ r1_tarski('#skF_1',B_96) ) ),
    inference(resolution,[status(thm)],[c_58,c_838])).

tff(c_99,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_107,plain,(
    ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_99,c_14])).

tff(c_1422,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_1413,c_107])).

tff(c_1432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_1422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:16:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.58  
% 3.26/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.58  %$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.26/1.58  
% 3.26/1.58  %Foreground sorts:
% 3.26/1.58  
% 3.26/1.58  
% 3.26/1.58  %Background operators:
% 3.26/1.58  
% 3.26/1.58  
% 3.26/1.58  %Foreground operators:
% 3.26/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.58  
% 3.26/1.59  tff(f_54, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_relset_1)).
% 3.26/1.59  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.26/1.59  tff(f_41, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 3.26/1.59  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.26/1.59  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.26/1.59  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.26/1.59  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.26/1.59  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.26/1.59  tff(c_20, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.26/1.59  tff(c_54, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.59  tff(c_58, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_54])).
% 3.26/1.59  tff(c_227, plain, (![A_35, C_36, B_37, D_38]: (r1_tarski(k2_zfmisc_1(A_35, C_36), k2_zfmisc_1(B_37, D_38)) | ~r1_tarski(C_36, D_38) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.59  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.59  tff(c_495, plain, (![A_50, C_51, B_52, D_53]: (k2_xboole_0(k2_zfmisc_1(A_50, C_51), k2_zfmisc_1(B_52, D_53))=k2_zfmisc_1(B_52, D_53) | ~r1_tarski(C_51, D_53) | ~r1_tarski(A_50, B_52))), inference(resolution, [status(thm)], [c_227, c_6])).
% 3.26/1.59  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.59  tff(c_108, plain, (![A_22, C_23, B_24]: (r1_tarski(A_22, k2_xboole_0(C_23, B_24)) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.59  tff(c_126, plain, (![A_22, A_1, B_2]: (r1_tarski(A_22, k2_xboole_0(A_1, B_2)) | ~r1_tarski(A_22, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_108])).
% 3.26/1.59  tff(c_838, plain, (![D_74, A_70, C_72, A_73, B_71]: (r1_tarski(A_70, k2_zfmisc_1(B_71, D_74)) | ~r1_tarski(A_70, k2_zfmisc_1(A_73, C_72)) | ~r1_tarski(C_72, D_74) | ~r1_tarski(A_73, B_71))), inference(superposition, [status(thm), theory('equality')], [c_495, c_126])).
% 3.26/1.59  tff(c_1413, plain, (![B_96, D_97]: (r1_tarski('#skF_5', k2_zfmisc_1(B_96, D_97)) | ~r1_tarski('#skF_3', D_97) | ~r1_tarski('#skF_1', B_96))), inference(resolution, [status(thm)], [c_58, c_838])).
% 3.26/1.59  tff(c_99, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.59  tff(c_14, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.26/1.59  tff(c_107, plain, (~r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_99, c_14])).
% 3.26/1.59  tff(c_1422, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_1413, c_107])).
% 3.26/1.59  tff(c_1432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_1422])).
% 3.26/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.59  
% 3.26/1.59  Inference rules
% 3.26/1.59  ----------------------
% 3.26/1.59  #Ref     : 0
% 3.26/1.59  #Sup     : 406
% 3.26/1.59  #Fact    : 0
% 3.26/1.59  #Define  : 0
% 3.26/1.59  #Split   : 8
% 3.26/1.59  #Chain   : 0
% 3.26/1.59  #Close   : 0
% 3.26/1.59  
% 3.26/1.59  Ordering : KBO
% 3.26/1.59  
% 3.26/1.59  Simplification rules
% 3.26/1.59  ----------------------
% 3.26/1.59  #Subsume      : 88
% 3.26/1.59  #Demod        : 62
% 3.26/1.59  #Tautology    : 73
% 3.26/1.59  #SimpNegUnit  : 0
% 3.26/1.59  #BackRed      : 0
% 3.26/1.59  
% 3.26/1.59  #Partial instantiations: 0
% 3.26/1.59  #Strategies tried      : 1
% 3.26/1.59  
% 3.26/1.59  Timing (in seconds)
% 3.26/1.59  ----------------------
% 3.26/1.60  Preprocessing        : 0.27
% 3.26/1.60  Parsing              : 0.15
% 3.26/1.60  CNF conversion       : 0.02
% 3.26/1.60  Main loop            : 0.52
% 3.26/1.60  Inferencing          : 0.18
% 3.26/1.60  Reduction            : 0.17
% 3.26/1.60  Demodulation         : 0.13
% 3.26/1.60  BG Simplification    : 0.02
% 3.26/1.60  Subsumption          : 0.11
% 3.26/1.60  Abstraction          : 0.02
% 3.26/1.60  MUC search           : 0.00
% 3.26/1.60  Cooper               : 0.00
% 3.26/1.60  Total                : 0.80
% 3.26/1.60  Index Insertion      : 0.00
% 3.26/1.60  Index Deletion       : 0.00
% 3.26/1.60  Index Matching       : 0.00
% 3.26/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
