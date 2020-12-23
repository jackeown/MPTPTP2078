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
% DateTime   : Thu Dec  3 09:58:12 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  69 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ( v3_setfam_1(B,A)
                & r1_tarski(C,B) )
             => v3_setfam_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_setfam_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27,plain,(
    ! [A_13,C_14,B_15] :
      ( r1_tarski(A_13,C_14)
      | ~ r1_tarski(B_15,C_14)
      | ~ r1_tarski(A_13,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_16] :
      ( r1_tarski(A_16,'#skF_2')
      | ~ r1_tarski(A_16,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_27])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | ~ r1_tarski(k1_tarski(A_4),B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    ! [A_17] :
      ( r2_hidden(A_17,'#skF_2')
      | ~ r1_tarski(k1_tarski(A_17),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_4])).

tff(c_48,plain,(
    ! [A_4] :
      ( r2_hidden(A_4,'#skF_2')
      | ~ r2_hidden(A_4,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_16,plain,(
    v3_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_71,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden(A_26,B_27)
      | ~ v3_setfam_1(B_27,A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | ~ v3_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_71])).

tff(c_80,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_74])).

tff(c_85,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_80])).

tff(c_12,plain,(
    ~ v3_setfam_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_86,plain,(
    ! [B_28,A_29] :
      ( v3_setfam_1(B_28,A_29)
      | r2_hidden(A_29,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_92,plain,
    ( v3_setfam_1('#skF_3','#skF_1')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_86])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_12,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:18:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.12  
% 1.62/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.12  %$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.62/1.12  
% 1.62/1.12  %Foreground sorts:
% 1.62/1.12  
% 1.62/1.12  
% 1.62/1.12  %Background operators:
% 1.62/1.12  
% 1.62/1.12  
% 1.62/1.12  %Foreground operators:
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.12  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 1.62/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.62/1.12  
% 1.62/1.13  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.62/1.13  tff(f_54, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((v3_setfam_1(B, A) & r1_tarski(C, B)) => v3_setfam_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_setfam_1)).
% 1.62/1.13  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.62/1.13  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_setfam_1)).
% 1.62/1.13  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.13  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.13  tff(c_27, plain, (![A_13, C_14, B_15]: (r1_tarski(A_13, C_14) | ~r1_tarski(B_15, C_14) | ~r1_tarski(A_13, B_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.13  tff(c_34, plain, (![A_16]: (r1_tarski(A_16, '#skF_2') | ~r1_tarski(A_16, '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_27])).
% 1.62/1.13  tff(c_4, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | ~r1_tarski(k1_tarski(A_4), B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.13  tff(c_43, plain, (![A_17]: (r2_hidden(A_17, '#skF_2') | ~r1_tarski(k1_tarski(A_17), '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_4])).
% 1.62/1.13  tff(c_48, plain, (![A_4]: (r2_hidden(A_4, '#skF_2') | ~r2_hidden(A_4, '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_43])).
% 1.62/1.13  tff(c_16, plain, (v3_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.13  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.13  tff(c_71, plain, (![A_26, B_27]: (~r2_hidden(A_26, B_27) | ~v3_setfam_1(B_27, A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.62/1.13  tff(c_74, plain, (~r2_hidden('#skF_1', '#skF_2') | ~v3_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_71])).
% 1.62/1.13  tff(c_80, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_74])).
% 1.62/1.13  tff(c_85, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_80])).
% 1.62/1.13  tff(c_12, plain, (~v3_setfam_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.13  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.13  tff(c_86, plain, (![B_28, A_29]: (v3_setfam_1(B_28, A_29) | r2_hidden(A_29, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.62/1.13  tff(c_92, plain, (v3_setfam_1('#skF_3', '#skF_1') | r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_86])).
% 1.62/1.13  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_12, c_92])).
% 1.62/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.13  
% 1.62/1.13  Inference rules
% 1.62/1.13  ----------------------
% 1.62/1.13  #Ref     : 0
% 1.62/1.13  #Sup     : 16
% 1.62/1.13  #Fact    : 0
% 1.62/1.13  #Define  : 0
% 1.62/1.13  #Split   : 1
% 1.62/1.13  #Chain   : 0
% 1.62/1.13  #Close   : 0
% 1.62/1.13  
% 1.62/1.13  Ordering : KBO
% 1.62/1.13  
% 1.62/1.13  Simplification rules
% 1.62/1.13  ----------------------
% 1.62/1.13  #Subsume      : 2
% 1.62/1.13  #Demod        : 3
% 1.62/1.13  #Tautology    : 3
% 1.62/1.13  #SimpNegUnit  : 2
% 1.62/1.13  #BackRed      : 0
% 1.62/1.13  
% 1.62/1.13  #Partial instantiations: 0
% 1.62/1.13  #Strategies tried      : 1
% 1.62/1.13  
% 1.62/1.13  Timing (in seconds)
% 1.62/1.13  ----------------------
% 1.62/1.14  Preprocessing        : 0.25
% 1.62/1.14  Parsing              : 0.14
% 1.62/1.14  CNF conversion       : 0.02
% 1.62/1.14  Main loop            : 0.13
% 1.62/1.14  Inferencing          : 0.05
% 1.62/1.14  Reduction            : 0.03
% 1.62/1.14  Demodulation         : 0.02
% 1.62/1.14  BG Simplification    : 0.01
% 1.62/1.14  Subsumption          : 0.03
% 1.62/1.14  Abstraction          : 0.00
% 1.62/1.14  MUC search           : 0.00
% 1.62/1.14  Cooper               : 0.00
% 1.62/1.14  Total                : 0.40
% 1.62/1.14  Index Insertion      : 0.00
% 1.62/1.14  Index Deletion       : 0.00
% 1.62/1.14  Index Matching       : 0.00
% 1.62/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
