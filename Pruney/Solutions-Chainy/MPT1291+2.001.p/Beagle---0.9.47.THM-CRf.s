%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:28 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   47 (  51 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  53 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( r1_tarski(C,B)
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_98,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_102,plain,(
    ~ r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_98,c_20])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_107,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_115,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_24,c_107])).

tff(c_12,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_83,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_145,plain,(
    ! [B_34,A_35] : k3_tarski(k2_tarski(B_34,A_35)) = k2_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_83])).

tff(c_14,plain,(
    ! [A_11,B_12] : k3_tarski(k2_tarski(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_172,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_14])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_70])).

tff(c_120,plain,(
    ! [A_32,B_33] : k2_xboole_0(A_32,k4_xboole_0(B_33,A_32)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_129,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_120])).

tff(c_132,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_129])).

tff(c_193,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_132])).

tff(c_296,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(k2_xboole_0(A_39,B_41),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_344,plain,(
    ! [C_43] :
      ( r1_tarski('#skF_3',C_43)
      | ~ r1_tarski('#skF_2',C_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_296])).

tff(c_347,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_115,c_344])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:25:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.22  
% 2.08/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.23  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.08/1.23  
% 2.08/1.23  %Foreground sorts:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Background operators:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Foreground operators:
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.23  
% 2.11/1.24  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.11/1.24  tff(f_56, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 2.11/1.24  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.11/1.24  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.11/1.24  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.11/1.24  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.11/1.24  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.11/1.24  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.11/1.24  tff(c_98, plain, (![A_28, B_29]: (m1_subset_1(A_28, k1_zfmisc_1(B_29)) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.24  tff(c_20, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.24  tff(c_102, plain, (~r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_98, c_20])).
% 2.11/1.24  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.24  tff(c_107, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.24  tff(c_115, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_107])).
% 2.11/1.24  tff(c_12, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.11/1.24  tff(c_83, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.24  tff(c_145, plain, (![B_34, A_35]: (k3_tarski(k2_tarski(B_34, A_35))=k2_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_12, c_83])).
% 2.11/1.24  tff(c_14, plain, (![A_11, B_12]: (k3_tarski(k2_tarski(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.24  tff(c_172, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_145, c_14])).
% 2.11/1.24  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.24  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.24  tff(c_70, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.24  tff(c_78, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_70])).
% 2.11/1.24  tff(c_120, plain, (![A_32, B_33]: (k2_xboole_0(A_32, k4_xboole_0(B_33, A_32))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.24  tff(c_129, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_78, c_120])).
% 2.11/1.24  tff(c_132, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_129])).
% 2.11/1.24  tff(c_193, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_172, c_132])).
% 2.11/1.24  tff(c_296, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(k2_xboole_0(A_39, B_41), C_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.24  tff(c_344, plain, (![C_43]: (r1_tarski('#skF_3', C_43) | ~r1_tarski('#skF_2', C_43))), inference(superposition, [status(thm), theory('equality')], [c_193, c_296])).
% 2.11/1.24  tff(c_347, plain, (r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_115, c_344])).
% 2.11/1.24  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_347])).
% 2.11/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  
% 2.11/1.24  Inference rules
% 2.11/1.24  ----------------------
% 2.11/1.24  #Ref     : 0
% 2.11/1.24  #Sup     : 85
% 2.11/1.24  #Fact    : 0
% 2.11/1.24  #Define  : 0
% 2.11/1.24  #Split   : 0
% 2.11/1.24  #Chain   : 0
% 2.11/1.24  #Close   : 0
% 2.11/1.24  
% 2.11/1.24  Ordering : KBO
% 2.11/1.24  
% 2.11/1.24  Simplification rules
% 2.11/1.24  ----------------------
% 2.11/1.24  #Subsume      : 2
% 2.11/1.24  #Demod        : 19
% 2.11/1.24  #Tautology    : 59
% 2.11/1.24  #SimpNegUnit  : 1
% 2.11/1.24  #BackRed      : 0
% 2.11/1.24  
% 2.11/1.24  #Partial instantiations: 0
% 2.11/1.24  #Strategies tried      : 1
% 2.11/1.24  
% 2.11/1.24  Timing (in seconds)
% 2.11/1.24  ----------------------
% 2.11/1.24  Preprocessing        : 0.27
% 2.11/1.24  Parsing              : 0.15
% 2.11/1.24  CNF conversion       : 0.02
% 2.11/1.24  Main loop            : 0.20
% 2.11/1.24  Inferencing          : 0.08
% 2.11/1.24  Reduction            : 0.07
% 2.11/1.24  Demodulation         : 0.05
% 2.11/1.24  BG Simplification    : 0.01
% 2.11/1.24  Subsumption          : 0.03
% 2.11/1.24  Abstraction          : 0.01
% 2.11/1.24  MUC search           : 0.00
% 2.11/1.24  Cooper               : 0.00
% 2.11/1.24  Total                : 0.50
% 2.11/1.24  Index Insertion      : 0.00
% 2.11/1.24  Index Deletion       : 0.00
% 2.11/1.24  Index Matching       : 0.00
% 2.11/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
