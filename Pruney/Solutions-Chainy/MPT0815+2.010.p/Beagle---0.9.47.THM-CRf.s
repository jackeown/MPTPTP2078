%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:54 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  26 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,D) )
       => m1_subset_1(k1_tarski(k4_tarski(A,C)),k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(c_14,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20))
      | ~ r2_hidden(B_18,D_20)
      | ~ r2_hidden(A_17,C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tarski(A_5),k1_zfmisc_1(B_6))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ~ m1_subset_1(k1_tarski(k4_tarski('#skF_1','#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_19,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_10])).

tff(c_31,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_19])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.36  
% 1.91/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.38  %$ r2_hidden > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.91/1.38  
% 1.91/1.38  %Foreground sorts:
% 1.91/1.38  
% 1.91/1.38  
% 1.91/1.38  %Background operators:
% 1.91/1.38  
% 1.91/1.38  
% 1.91/1.38  %Foreground operators:
% 1.91/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.91/1.38  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.38  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.38  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.38  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.38  
% 2.03/1.39  tff(f_42, negated_conjecture, ~(![A, B, C, D]: ((r2_hidden(A, B) & r2_hidden(C, D)) => m1_subset_1(k1_tarski(k4_tarski(A, C)), k1_zfmisc_1(k2_zfmisc_1(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_relset_1)).
% 2.03/1.39  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 2.03/1.39  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.03/1.39  tff(c_14, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.03/1.39  tff(c_12, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.03/1.39  tff(c_22, plain, (![A_17, B_18, C_19, D_20]: (r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)) | ~r2_hidden(B_18, D_20) | ~r2_hidden(A_17, C_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.39  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k1_tarski(A_5), k1_zfmisc_1(B_6)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.39  tff(c_10, plain, (~m1_subset_1(k1_tarski(k4_tarski('#skF_1', '#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.03/1.39  tff(c_19, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_10])).
% 2.03/1.39  tff(c_31, plain, (~r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_19])).
% 2.03/1.39  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_31])).
% 2.03/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.39  
% 2.03/1.39  Inference rules
% 2.03/1.39  ----------------------
% 2.03/1.39  #Ref     : 0
% 2.03/1.39  #Sup     : 4
% 2.03/1.39  #Fact    : 0
% 2.03/1.39  #Define  : 0
% 2.03/1.39  #Split   : 0
% 2.03/1.39  #Chain   : 0
% 2.03/1.39  #Close   : 0
% 2.03/1.39  
% 2.03/1.39  Ordering : KBO
% 2.03/1.39  
% 2.03/1.39  Simplification rules
% 2.03/1.39  ----------------------
% 2.03/1.39  #Subsume      : 0
% 2.03/1.39  #Demod        : 2
% 2.03/1.39  #Tautology    : 2
% 2.03/1.39  #SimpNegUnit  : 0
% 2.03/1.39  #BackRed      : 0
% 2.03/1.39  
% 2.03/1.39  #Partial instantiations: 0
% 2.03/1.39  #Strategies tried      : 1
% 2.03/1.39  
% 2.03/1.39  Timing (in seconds)
% 2.03/1.39  ----------------------
% 2.03/1.40  Preprocessing        : 0.42
% 2.03/1.40  Parsing              : 0.23
% 2.03/1.40  CNF conversion       : 0.03
% 2.03/1.40  Main loop            : 0.14
% 2.03/1.40  Inferencing          : 0.06
% 2.03/1.40  Reduction            : 0.04
% 2.03/1.40  Demodulation         : 0.03
% 2.03/1.40  BG Simplification    : 0.01
% 2.03/1.40  Subsumption          : 0.02
% 2.03/1.40  Abstraction          : 0.01
% 2.03/1.40  MUC search           : 0.00
% 2.03/1.40  Cooper               : 0.00
% 2.03/1.40  Total                : 0.61
% 2.03/1.40  Index Insertion      : 0.00
% 2.03/1.40  Index Deletion       : 0.00
% 2.03/1.40  Index Matching       : 0.00
% 2.03/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
