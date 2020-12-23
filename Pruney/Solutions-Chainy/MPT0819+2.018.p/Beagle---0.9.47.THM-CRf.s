%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:00 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 (  72 expanded)
%              Number of equality atoms :    4 (   6 expanded)
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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(k2_zfmisc_1(A_6,C_8),k2_zfmisc_1(B_7,C_8))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [C_29,A_30,B_31] :
      ( r1_tarski(k2_zfmisc_1(C_29,A_30),k2_zfmisc_1(C_29,B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_30])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    k2_xboole_0('#skF_5',k2_zfmisc_1('#skF_1','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_4])).

tff(c_60,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(A_17,C_18)
      | ~ r1_tarski(k2_xboole_0(A_17,B_19),C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [C_18] :
      ( r1_tarski('#skF_5',C_18)
      | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),C_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_60])).

tff(c_123,plain,(
    ! [B_32] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_1',B_32))
      | ~ r1_tarski('#skF_3',B_32) ) ),
    inference(resolution,[status(thm)],[c_113,c_63])).

tff(c_128,plain,(
    ! [B_33] :
      ( k2_xboole_0('#skF_5',k2_zfmisc_1('#skF_1',B_33)) = k2_zfmisc_1('#skF_1',B_33)
      | ~ r1_tarski('#skF_3',B_33) ) ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_169,plain,(
    ! [C_36,B_37] :
      ( r1_tarski('#skF_5',C_36)
      | ~ r1_tarski(k2_zfmisc_1('#skF_1',B_37),C_36)
      | ~ r1_tarski('#skF_3',B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_2])).

tff(c_201,plain,(
    ! [B_44,C_45] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(B_44,C_45))
      | ~ r1_tarski('#skF_3',C_45)
      | ~ r1_tarski('#skF_1',B_44) ) ),
    inference(resolution,[status(thm)],[c_8,c_169])).

tff(c_51,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_59,plain,(
    ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_51,c_14])).

tff(c_204,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_201,c_59])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  %$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.99/1.25  
% 1.99/1.25  %Foreground sorts:
% 1.99/1.25  
% 1.99/1.25  
% 1.99/1.25  %Background operators:
% 1.99/1.25  
% 1.99/1.25  
% 1.99/1.25  %Foreground operators:
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.25  
% 1.99/1.26  tff(f_52, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 1.99/1.26  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 1.99/1.26  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.99/1.26  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.99/1.26  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.99/1.26  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.26  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.26  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(k2_zfmisc_1(A_6, C_8), k2_zfmisc_1(B_7, C_8)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.26  tff(c_113, plain, (![C_29, A_30, B_31]: (r1_tarski(k2_zfmisc_1(C_29, A_30), k2_zfmisc_1(C_29, B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.26  tff(c_20, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.26  tff(c_30, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.99/1.26  tff(c_34, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_30])).
% 1.99/1.26  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.26  tff(c_46, plain, (k2_xboole_0('#skF_5', k2_zfmisc_1('#skF_1', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_4])).
% 1.99/1.26  tff(c_60, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, C_18) | ~r1_tarski(k2_xboole_0(A_17, B_19), C_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.26  tff(c_63, plain, (![C_18]: (r1_tarski('#skF_5', C_18) | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), C_18))), inference(superposition, [status(thm), theory('equality')], [c_46, c_60])).
% 1.99/1.26  tff(c_123, plain, (![B_32]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_1', B_32)) | ~r1_tarski('#skF_3', B_32))), inference(resolution, [status(thm)], [c_113, c_63])).
% 1.99/1.26  tff(c_128, plain, (![B_33]: (k2_xboole_0('#skF_5', k2_zfmisc_1('#skF_1', B_33))=k2_zfmisc_1('#skF_1', B_33) | ~r1_tarski('#skF_3', B_33))), inference(resolution, [status(thm)], [c_123, c_4])).
% 1.99/1.26  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.26  tff(c_169, plain, (![C_36, B_37]: (r1_tarski('#skF_5', C_36) | ~r1_tarski(k2_zfmisc_1('#skF_1', B_37), C_36) | ~r1_tarski('#skF_3', B_37))), inference(superposition, [status(thm), theory('equality')], [c_128, c_2])).
% 1.99/1.26  tff(c_201, plain, (![B_44, C_45]: (r1_tarski('#skF_5', k2_zfmisc_1(B_44, C_45)) | ~r1_tarski('#skF_3', C_45) | ~r1_tarski('#skF_1', B_44))), inference(resolution, [status(thm)], [c_8, c_169])).
% 1.99/1.26  tff(c_51, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.99/1.26  tff(c_14, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.26  tff(c_59, plain, (~r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_51, c_14])).
% 1.99/1.26  tff(c_204, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_201, c_59])).
% 1.99/1.26  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_204])).
% 1.99/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.26  
% 1.99/1.26  Inference rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Ref     : 0
% 1.99/1.26  #Sup     : 45
% 1.99/1.26  #Fact    : 0
% 1.99/1.26  #Define  : 0
% 1.99/1.26  #Split   : 0
% 1.99/1.26  #Chain   : 0
% 1.99/1.26  #Close   : 0
% 1.99/1.26  
% 1.99/1.26  Ordering : KBO
% 1.99/1.26  
% 1.99/1.26  Simplification rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Subsume      : 0
% 1.99/1.26  #Demod        : 2
% 1.99/1.26  #Tautology    : 19
% 1.99/1.26  #SimpNegUnit  : 0
% 1.99/1.26  #BackRed      : 0
% 1.99/1.26  
% 1.99/1.26  #Partial instantiations: 0
% 1.99/1.26  #Strategies tried      : 1
% 1.99/1.26  
% 1.99/1.26  Timing (in seconds)
% 1.99/1.26  ----------------------
% 1.99/1.26  Preprocessing        : 0.23
% 1.99/1.26  Parsing              : 0.13
% 1.99/1.26  CNF conversion       : 0.02
% 1.99/1.26  Main loop            : 0.19
% 1.99/1.26  Inferencing          : 0.08
% 1.99/1.26  Reduction            : 0.05
% 1.99/1.26  Demodulation         : 0.03
% 1.99/1.26  BG Simplification    : 0.01
% 1.99/1.26  Subsumption          : 0.04
% 1.99/1.27  Abstraction          : 0.01
% 1.99/1.27  MUC search           : 0.00
% 1.99/1.27  Cooper               : 0.00
% 1.99/1.27  Total                : 0.45
% 1.99/1.27  Index Insertion      : 0.00
% 1.99/1.27  Index Deletion       : 0.00
% 1.99/1.27  Index Matching       : 0.00
% 1.99/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
