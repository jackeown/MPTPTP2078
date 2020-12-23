%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:28 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > #nlpp > u1_struct_0 > k9_setfam_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_43,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => r1_tarski(B,k9_setfam_1(k2_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tops_2)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_6,plain,(
    ! [A_3] : k9_setfam_1(A_3) = k1_zfmisc_1(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ~ r1_tarski('#skF_2',k9_setfam_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_15,plain,(
    ~ r1_tarski('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_14,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_25,plain,(
    ! [A_7] :
      ( u1_struct_0(A_7) = k2_struct_0(A_7)
      | ~ l1_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_25])).

tff(c_12,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_31,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_12])).

tff(c_36,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_31,c_36])).

tff(c_46,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 18:23:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.08  
% 1.53/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.08  %$ r1_tarski > m1_subset_1 > l1_struct_0 > #nlpp > u1_struct_0 > k9_setfam_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.53/1.08  
% 1.53/1.08  %Foreground sorts:
% 1.53/1.08  
% 1.53/1.08  
% 1.53/1.08  %Background operators:
% 1.53/1.08  
% 1.53/1.08  
% 1.53/1.08  %Foreground operators:
% 1.53/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.53/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.53/1.08  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.53/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.53/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.53/1.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.53/1.08  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.53/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.53/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.53/1.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.53/1.08  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.53/1.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.53/1.08  
% 1.53/1.09  tff(f_31, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.53/1.09  tff(f_43, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(B, k9_setfam_1(k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tops_2)).
% 1.53/1.09  tff(f_35, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 1.53/1.09  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.53/1.09  tff(c_6, plain, (![A_3]: (k9_setfam_1(A_3)=k1_zfmisc_1(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.53/1.09  tff(c_10, plain, (~r1_tarski('#skF_2', k9_setfam_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.53/1.09  tff(c_15, plain, (~r1_tarski('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 1.53/1.09  tff(c_14, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.53/1.09  tff(c_25, plain, (![A_7]: (u1_struct_0(A_7)=k2_struct_0(A_7) | ~l1_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.53/1.09  tff(c_29, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_25])).
% 1.53/1.09  tff(c_12, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.53/1.09  tff(c_31, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_12])).
% 1.53/1.09  tff(c_36, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.53/1.09  tff(c_39, plain, (r1_tarski('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_31, c_36])).
% 1.53/1.09  tff(c_46, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15, c_39])).
% 1.53/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.53/1.09  
% 1.53/1.09  Inference rules
% 1.53/1.09  ----------------------
% 1.53/1.09  #Ref     : 0
% 1.53/1.09  #Sup     : 7
% 1.53/1.09  #Fact    : 0
% 1.53/1.09  #Define  : 0
% 1.53/1.09  #Split   : 0
% 1.53/1.09  #Chain   : 0
% 1.53/1.09  #Close   : 0
% 1.53/1.09  
% 1.53/1.09  Ordering : KBO
% 1.53/1.09  
% 1.53/1.09  Simplification rules
% 1.53/1.09  ----------------------
% 1.53/1.09  #Subsume      : 0
% 1.53/1.09  #Demod        : 2
% 1.53/1.09  #Tautology    : 4
% 1.53/1.09  #SimpNegUnit  : 1
% 1.53/1.09  #BackRed      : 1
% 1.53/1.09  
% 1.53/1.09  #Partial instantiations: 0
% 1.53/1.09  #Strategies tried      : 1
% 1.53/1.09  
% 1.53/1.09  Timing (in seconds)
% 1.53/1.09  ----------------------
% 1.64/1.09  Preprocessing        : 0.26
% 1.64/1.09  Parsing              : 0.14
% 1.64/1.09  CNF conversion       : 0.01
% 1.64/1.09  Main loop            : 0.07
% 1.64/1.09  Inferencing          : 0.03
% 1.64/1.09  Reduction            : 0.02
% 1.64/1.09  Demodulation         : 0.02
% 1.64/1.09  BG Simplification    : 0.01
% 1.64/1.09  Subsumption          : 0.01
% 1.64/1.09  Abstraction          : 0.01
% 1.64/1.09  MUC search           : 0.00
% 1.64/1.10  Cooper               : 0.00
% 1.64/1.10  Total                : 0.35
% 1.64/1.10  Index Insertion      : 0.00
% 1.64/1.10  Index Deletion       : 0.00
% 1.64/1.10  Index Matching       : 0.00
% 1.64/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
