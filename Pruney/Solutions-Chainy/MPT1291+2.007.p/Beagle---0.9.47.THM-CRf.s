%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:29 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  35 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( r1_tarski(C,B)
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).

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
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12,c_20])).

tff(c_29,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_tarski(A_14,C_15)
      | ~ r1_tarski(B_16,C_15)
      | ~ r1_tarski(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_18,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_29])).

tff(c_15,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19,plain,(
    ~ r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_15,c_8])).

tff(c_45,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_19])).

tff(c_50,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:20:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.48/1.04  
% 1.48/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.04  %$ r1_tarski > m1_subset_1 > l1_struct_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.61/1.04  
% 1.61/1.04  %Foreground sorts:
% 1.61/1.04  
% 1.61/1.04  
% 1.61/1.04  %Background operators:
% 1.61/1.04  
% 1.61/1.04  
% 1.61/1.04  %Foreground operators:
% 1.61/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.04  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.04  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.61/1.04  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.61/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.61/1.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.61/1.04  
% 1.61/1.05  tff(f_46, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_tops_2)).
% 1.61/1.05  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.61/1.05  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.61/1.05  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.05  tff(c_12, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.05  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.61/1.05  tff(c_28, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_20])).
% 1.61/1.05  tff(c_29, plain, (![A_14, C_15, B_16]: (r1_tarski(A_14, C_15) | ~r1_tarski(B_16, C_15) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.05  tff(c_40, plain, (![A_18]: (r1_tarski(A_18, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_18, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_29])).
% 1.61/1.05  tff(c_15, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.61/1.05  tff(c_8, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.05  tff(c_19, plain, (~r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_15, c_8])).
% 1.61/1.05  tff(c_45, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_19])).
% 1.61/1.05  tff(c_50, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_45])).
% 1.61/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.05  
% 1.61/1.05  Inference rules
% 1.61/1.05  ----------------------
% 1.61/1.05  #Ref     : 0
% 1.61/1.05  #Sup     : 8
% 1.61/1.05  #Fact    : 0
% 1.61/1.05  #Define  : 0
% 1.61/1.05  #Split   : 0
% 1.61/1.05  #Chain   : 0
% 1.61/1.05  #Close   : 0
% 1.61/1.05  
% 1.61/1.05  Ordering : KBO
% 1.61/1.05  
% 1.61/1.05  Simplification rules
% 1.61/1.05  ----------------------
% 1.61/1.05  #Subsume      : 0
% 1.61/1.05  #Demod        : 1
% 1.61/1.05  #Tautology    : 1
% 1.61/1.05  #SimpNegUnit  : 0
% 1.61/1.05  #BackRed      : 0
% 1.61/1.05  
% 1.61/1.05  #Partial instantiations: 0
% 1.61/1.05  #Strategies tried      : 1
% 1.61/1.05  
% 1.61/1.05  Timing (in seconds)
% 1.61/1.05  ----------------------
% 1.61/1.05  Preprocessing        : 0.26
% 1.61/1.05  Parsing              : 0.15
% 1.61/1.05  CNF conversion       : 0.02
% 1.61/1.05  Main loop            : 0.09
% 1.61/1.05  Inferencing          : 0.04
% 1.61/1.05  Reduction            : 0.02
% 1.61/1.05  Demodulation         : 0.02
% 1.61/1.05  BG Simplification    : 0.01
% 1.61/1.05  Subsumption          : 0.01
% 1.61/1.05  Abstraction          : 0.00
% 1.61/1.05  MUC search           : 0.00
% 1.61/1.05  Cooper               : 0.00
% 1.61/1.05  Total                : 0.37
% 1.61/1.05  Index Insertion      : 0.00
% 1.61/1.05  Index Deletion       : 0.00
% 1.61/1.05  Index Matching       : 0.00
% 1.61/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
