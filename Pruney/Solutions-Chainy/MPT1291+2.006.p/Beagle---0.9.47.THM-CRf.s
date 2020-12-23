%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:29 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  38 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( r1_tarski(C,B)
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_17,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21,plain,(
    ~ r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_17,c_10])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_31,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_39,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14,c_31])).

tff(c_12,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_22])).

tff(c_44,plain,(
    ! [A_18,C_19,B_20] :
      ( r1_tarski(A_18,C_19)
      | ~ r1_tarski(k2_xboole_0(A_18,B_20),C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [C_21] :
      ( r1_tarski('#skF_3',C_21)
      | ~ r1_tarski('#skF_2',C_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_44])).

tff(c_51,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_39,c_48])).

tff(c_55,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21,c_51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.67/1.11  
% 1.67/1.11  %Foreground sorts:
% 1.67/1.11  
% 1.67/1.11  
% 1.67/1.11  %Background operators:
% 1.67/1.11  
% 1.67/1.11  
% 1.67/1.11  %Foreground operators:
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.11  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.67/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.11  
% 1.67/1.12  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.67/1.12  tff(f_48, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 1.67/1.12  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.67/1.12  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.67/1.12  tff(c_17, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.12  tff(c_10, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.12  tff(c_21, plain, (~r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_17, c_10])).
% 1.67/1.12  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.12  tff(c_31, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.12  tff(c_39, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_31])).
% 1.67/1.12  tff(c_12, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.12  tff(c_22, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.12  tff(c_26, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_12, c_22])).
% 1.67/1.12  tff(c_44, plain, (![A_18, C_19, B_20]: (r1_tarski(A_18, C_19) | ~r1_tarski(k2_xboole_0(A_18, B_20), C_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.12  tff(c_48, plain, (![C_21]: (r1_tarski('#skF_3', C_21) | ~r1_tarski('#skF_2', C_21))), inference(superposition, [status(thm), theory('equality')], [c_26, c_44])).
% 1.67/1.12  tff(c_51, plain, (r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_39, c_48])).
% 1.67/1.12  tff(c_55, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21, c_51])).
% 1.67/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  Inference rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Ref     : 0
% 1.67/1.12  #Sup     : 9
% 1.67/1.12  #Fact    : 0
% 1.67/1.12  #Define  : 0
% 1.67/1.12  #Split   : 0
% 1.67/1.12  #Chain   : 0
% 1.67/1.12  #Close   : 0
% 1.67/1.12  
% 1.67/1.12  Ordering : KBO
% 1.67/1.12  
% 1.67/1.12  Simplification rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Subsume      : 0
% 1.67/1.12  #Demod        : 0
% 1.67/1.12  #Tautology    : 3
% 1.67/1.12  #SimpNegUnit  : 1
% 1.67/1.12  #BackRed      : 0
% 1.67/1.12  
% 1.67/1.12  #Partial instantiations: 0
% 1.67/1.12  #Strategies tried      : 1
% 1.67/1.12  
% 1.67/1.12  Timing (in seconds)
% 1.67/1.12  ----------------------
% 1.67/1.12  Preprocessing        : 0.26
% 1.67/1.12  Parsing              : 0.15
% 1.67/1.12  CNF conversion       : 0.02
% 1.67/1.12  Main loop            : 0.09
% 1.67/1.12  Inferencing          : 0.04
% 1.67/1.12  Reduction            : 0.02
% 1.67/1.12  Demodulation         : 0.01
% 1.67/1.12  BG Simplification    : 0.01
% 1.67/1.12  Subsumption          : 0.01
% 1.67/1.12  Abstraction          : 0.00
% 1.67/1.12  MUC search           : 0.00
% 1.67/1.12  Cooper               : 0.00
% 1.67/1.12  Total                : 0.38
% 1.67/1.12  Index Insertion      : 0.00
% 1.67/1.12  Index Deletion       : 0.00
% 1.67/1.12  Index Matching       : 0.00
% 1.67/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
