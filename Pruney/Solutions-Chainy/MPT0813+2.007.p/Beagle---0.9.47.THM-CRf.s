%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:51 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  32 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ( r1_tarski(A,D)
         => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_18])).

tff(c_27,plain,(
    ! [A_10,C_11,B_12] :
      ( r1_tarski(A_10,C_11)
      | ~ r1_tarski(B_12,C_11)
      | ~ r1_tarski(A_10,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_14,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_27])).

tff(c_13,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_13,c_8])).

tff(c_40,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_35,c_17])).

tff(c_45,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.06  
% 1.52/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.06  %$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.52/1.06  
% 1.52/1.06  %Foreground sorts:
% 1.52/1.06  
% 1.52/1.06  
% 1.52/1.06  %Background operators:
% 1.52/1.06  
% 1.52/1.06  
% 1.52/1.06  %Foreground operators:
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.52/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.52/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.52/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.52/1.06  tff('#skF_4', type, '#skF_4': $i).
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.52/1.06  
% 1.52/1.07  tff(f_42, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 1.52/1.07  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.52/1.07  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.52/1.07  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.52/1.07  tff(c_12, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.52/1.07  tff(c_18, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.52/1.07  tff(c_26, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_18])).
% 1.52/1.07  tff(c_27, plain, (![A_10, C_11, B_12]: (r1_tarski(A_10, C_11) | ~r1_tarski(B_12, C_11) | ~r1_tarski(A_10, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.52/1.07  tff(c_35, plain, (![A_14]: (r1_tarski(A_14, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_14, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_27])).
% 1.52/1.07  tff(c_13, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.52/1.07  tff(c_8, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.52/1.07  tff(c_17, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_13, c_8])).
% 1.52/1.07  tff(c_40, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_35, c_17])).
% 1.52/1.07  tff(c_45, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_40])).
% 1.52/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.07  
% 1.52/1.07  Inference rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Ref     : 0
% 1.52/1.07  #Sup     : 7
% 1.52/1.07  #Fact    : 0
% 1.52/1.07  #Define  : 0
% 1.52/1.07  #Split   : 0
% 1.52/1.07  #Chain   : 0
% 1.52/1.07  #Close   : 0
% 1.52/1.07  
% 1.52/1.07  Ordering : KBO
% 1.52/1.07  
% 1.52/1.07  Simplification rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Subsume      : 0
% 1.52/1.07  #Demod        : 1
% 1.52/1.07  #Tautology    : 1
% 1.52/1.07  #SimpNegUnit  : 0
% 1.52/1.07  #BackRed      : 0
% 1.52/1.07  
% 1.52/1.07  #Partial instantiations: 0
% 1.52/1.07  #Strategies tried      : 1
% 1.52/1.07  
% 1.52/1.07  Timing (in seconds)
% 1.52/1.07  ----------------------
% 1.52/1.07  Preprocessing        : 0.24
% 1.52/1.07  Parsing              : 0.14
% 1.52/1.07  CNF conversion       : 0.01
% 1.52/1.07  Main loop            : 0.09
% 1.52/1.07  Inferencing          : 0.04
% 1.52/1.07  Reduction            : 0.02
% 1.52/1.07  Demodulation         : 0.02
% 1.52/1.07  BG Simplification    : 0.01
% 1.52/1.07  Subsumption          : 0.01
% 1.52/1.07  Abstraction          : 0.00
% 1.52/1.07  MUC search           : 0.00
% 1.52/1.07  Cooper               : 0.00
% 1.52/1.07  Total                : 0.35
% 1.52/1.07  Index Insertion      : 0.00
% 1.52/1.07  Index Deletion       : 0.00
% 1.52/1.07  Index Matching       : 0.00
% 1.52/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
