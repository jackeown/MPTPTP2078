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
% DateTime   : Thu Dec  3 09:58:12 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  64 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ( v3_setfam_1(B,A)
                & r1_tarski(C,B) )
             => v3_setfam_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ~ v3_setfam_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    ! [B_21,A_22] :
      ( v3_setfam_1(B_21,A_22)
      | r2_hidden(A_22,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,
    ( v3_setfam_1('#skF_3','#skF_1')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_80,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_73])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_1',A_25)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_110,plain,(
    ! [B_26] :
      ( r2_hidden('#skF_1',B_26)
      | ~ r1_tarski('#skF_3',B_26) ) ),
    inference(resolution,[status(thm)],[c_10,c_97])).

tff(c_16,plain,(
    v3_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    ! [A_17,B_18] :
      ( ~ r2_hidden(A_17,B_18)
      | ~ v3_setfam_1(B_18,A_17)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | ~ v3_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_36])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_43])).

tff(c_113,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_110,c_50])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.13  %$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.69/1.13  
% 1.69/1.13  %Foreground sorts:
% 1.69/1.13  
% 1.69/1.13  
% 1.69/1.13  %Background operators:
% 1.69/1.13  
% 1.69/1.13  
% 1.69/1.13  %Foreground operators:
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.13  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 1.69/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.69/1.13  
% 1.69/1.14  tff(f_55, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((v3_setfam_1(B, A) & r1_tarski(C, B)) => v3_setfam_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_setfam_1)).
% 1.69/1.14  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.69/1.14  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_setfam_1)).
% 1.69/1.14  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 1.69/1.14  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.69/1.14  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.69/1.14  tff(c_12, plain, (~v3_setfam_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.69/1.14  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.69/1.14  tff(c_63, plain, (![B_21, A_22]: (v3_setfam_1(B_21, A_22) | r2_hidden(A_22, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.69/1.14  tff(c_73, plain, (v3_setfam_1('#skF_3', '#skF_1') | r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_63])).
% 1.69/1.14  tff(c_80, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_12, c_73])).
% 1.69/1.14  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.69/1.14  tff(c_97, plain, (![A_25]: (r2_hidden('#skF_1', A_25) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_25)))), inference(resolution, [status(thm)], [c_80, c_2])).
% 1.69/1.14  tff(c_110, plain, (![B_26]: (r2_hidden('#skF_1', B_26) | ~r1_tarski('#skF_3', B_26))), inference(resolution, [status(thm)], [c_10, c_97])).
% 1.69/1.14  tff(c_16, plain, (v3_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.69/1.14  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.69/1.14  tff(c_36, plain, (![A_17, B_18]: (~r2_hidden(A_17, B_18) | ~v3_setfam_1(B_18, A_17) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.69/1.14  tff(c_43, plain, (~r2_hidden('#skF_1', '#skF_2') | ~v3_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_36])).
% 1.69/1.14  tff(c_50, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_43])).
% 1.69/1.14  tff(c_113, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_110, c_50])).
% 1.69/1.14  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_113])).
% 1.69/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.14  
% 1.69/1.14  Inference rules
% 1.69/1.14  ----------------------
% 1.69/1.14  #Ref     : 0
% 1.69/1.14  #Sup     : 19
% 1.69/1.14  #Fact    : 0
% 1.69/1.14  #Define  : 0
% 1.69/1.14  #Split   : 0
% 1.69/1.14  #Chain   : 0
% 1.69/1.14  #Close   : 0
% 1.69/1.14  
% 1.69/1.14  Ordering : KBO
% 1.69/1.14  
% 1.69/1.14  Simplification rules
% 1.69/1.14  ----------------------
% 1.69/1.14  #Subsume      : 3
% 1.69/1.14  #Demod        : 6
% 1.69/1.14  #Tautology    : 4
% 1.69/1.14  #SimpNegUnit  : 4
% 1.69/1.14  #BackRed      : 0
% 1.69/1.14  
% 1.69/1.14  #Partial instantiations: 0
% 1.69/1.14  #Strategies tried      : 1
% 1.69/1.14  
% 1.69/1.14  Timing (in seconds)
% 1.69/1.14  ----------------------
% 1.69/1.14  Preprocessing        : 0.26
% 1.69/1.14  Parsing              : 0.14
% 1.69/1.14  CNF conversion       : 0.02
% 1.69/1.14  Main loop            : 0.13
% 1.69/1.14  Inferencing          : 0.06
% 1.69/1.14  Reduction            : 0.03
% 1.69/1.14  Demodulation         : 0.03
% 1.69/1.14  BG Simplification    : 0.01
% 1.69/1.14  Subsumption          : 0.02
% 1.69/1.14  Abstraction          : 0.01
% 1.69/1.14  MUC search           : 0.00
% 1.69/1.14  Cooper               : 0.00
% 1.69/1.14  Total                : 0.41
% 1.69/1.14  Index Insertion      : 0.00
% 1.69/1.14  Index Deletion       : 0.00
% 1.69/1.14  Index Matching       : 0.00
% 1.69/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
