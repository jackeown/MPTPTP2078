%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:11 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  58 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ( v3_setfam_1(B,A)
                & r1_tarski(C,B) )
             => v3_setfam_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ~ v3_setfam_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    ! [B_19,A_20] :
      ( v3_setfam_1(B_19,A_20)
      | r2_hidden(A_20,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,
    ( v3_setfam_1('#skF_4','#skF_2')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_44])).

tff(c_56,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_50])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [B_21] :
      ( r2_hidden('#skF_2',B_21)
      | ~ r1_tarski('#skF_4',B_21) ) ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_16,plain,(
    v3_setfam_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_33,plain,(
    ! [A_17,B_18] :
      ( ~ r2_hidden(A_17,B_18)
      | ~ v3_setfam_1(B_18,A_17)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ v3_setfam_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_33])).

tff(c_42,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_36])).

tff(c_63,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_42])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.22  
% 1.78/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.22  %$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.78/1.22  
% 1.78/1.22  %Foreground sorts:
% 1.78/1.22  
% 1.78/1.22  
% 1.78/1.22  %Background operators:
% 1.78/1.22  
% 1.78/1.22  
% 1.78/1.22  %Foreground operators:
% 1.78/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.78/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.78/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.22  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 1.78/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.78/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.78/1.22  
% 1.88/1.23  tff(f_51, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((v3_setfam_1(B, A) & r1_tarski(C, B)) => v3_setfam_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_setfam_1)).
% 1.88/1.23  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 1.88/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.88/1.23  tff(c_14, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.23  tff(c_12, plain, (~v3_setfam_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.23  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.23  tff(c_44, plain, (![B_19, A_20]: (v3_setfam_1(B_19, A_20) | r2_hidden(A_20, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.23  tff(c_50, plain, (v3_setfam_1('#skF_4', '#skF_2') | r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_44])).
% 1.88/1.23  tff(c_56, plain, (r2_hidden('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_12, c_50])).
% 1.88/1.23  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.23  tff(c_60, plain, (![B_21]: (r2_hidden('#skF_2', B_21) | ~r1_tarski('#skF_4', B_21))), inference(resolution, [status(thm)], [c_56, c_2])).
% 1.88/1.23  tff(c_16, plain, (v3_setfam_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.23  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.23  tff(c_33, plain, (![A_17, B_18]: (~r2_hidden(A_17, B_18) | ~v3_setfam_1(B_18, A_17) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.23  tff(c_36, plain, (~r2_hidden('#skF_2', '#skF_3') | ~v3_setfam_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_33])).
% 1.88/1.23  tff(c_42, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_36])).
% 1.88/1.23  tff(c_63, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_42])).
% 1.88/1.23  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_63])).
% 1.88/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.23  
% 1.88/1.23  Inference rules
% 1.88/1.23  ----------------------
% 1.88/1.23  #Ref     : 0
% 1.88/1.23  #Sup     : 9
% 1.88/1.23  #Fact    : 0
% 1.88/1.23  #Define  : 0
% 1.88/1.23  #Split   : 0
% 1.88/1.23  #Chain   : 0
% 1.88/1.23  #Close   : 0
% 1.88/1.24  
% 1.88/1.24  Ordering : KBO
% 1.88/1.24  
% 1.88/1.24  Simplification rules
% 1.88/1.24  ----------------------
% 1.88/1.24  #Subsume      : 1
% 1.88/1.24  #Demod        : 3
% 1.88/1.24  #Tautology    : 1
% 1.88/1.24  #SimpNegUnit  : 2
% 1.88/1.24  #BackRed      : 0
% 1.88/1.24  
% 1.88/1.24  #Partial instantiations: 0
% 1.88/1.24  #Strategies tried      : 1
% 1.88/1.24  
% 1.88/1.24  Timing (in seconds)
% 1.88/1.24  ----------------------
% 1.88/1.24  Preprocessing        : 0.34
% 1.88/1.24  Parsing              : 0.21
% 1.88/1.24  CNF conversion       : 0.02
% 1.88/1.24  Main loop            : 0.12
% 1.88/1.24  Inferencing          : 0.06
% 1.88/1.24  Reduction            : 0.03
% 1.88/1.24  Demodulation         : 0.02
% 1.88/1.24  BG Simplification    : 0.01
% 1.88/1.24  Subsumption          : 0.02
% 1.88/1.24  Abstraction          : 0.00
% 1.88/1.24  MUC search           : 0.00
% 1.88/1.24  Cooper               : 0.00
% 1.88/1.24  Total                : 0.49
% 1.88/1.24  Index Insertion      : 0.00
% 1.88/1.24  Index Deletion       : 0.00
% 1.88/1.24  Index Matching       : 0.00
% 1.88/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
