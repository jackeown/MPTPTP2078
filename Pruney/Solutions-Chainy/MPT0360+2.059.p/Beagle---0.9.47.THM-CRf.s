%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:26 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_36])).

tff(c_18,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_125,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k3_subset_1(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_129,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_125])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_xboole_0(A_26,C_27)
      | ~ r1_xboole_0(B_28,C_27)
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [A_26,B_11,A_10] :
      ( r1_xboole_0(A_26,B_11)
      | ~ r1_tarski(A_26,k4_xboole_0(A_10,B_11)) ) ),
    inference(resolution,[status(thm)],[c_12,c_95])).

tff(c_173,plain,(
    ! [A_39] :
      ( r1_xboole_0(A_39,'#skF_3')
      | ~ r1_tarski(A_39,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_104])).

tff(c_177,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_173])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_182,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_177,c_2])).

tff(c_185,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_182])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:23:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.18  
% 1.71/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.18  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.71/1.18  
% 1.71/1.18  %Foreground sorts:
% 1.71/1.18  
% 1.71/1.18  
% 1.71/1.18  %Background operators:
% 1.71/1.18  
% 1.71/1.18  
% 1.71/1.18  %Foreground operators:
% 1.71/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.71/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.18  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.71/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.71/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.71/1.18  
% 1.97/1.19  tff(f_56, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 1.97/1.19  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.97/1.19  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.97/1.19  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.97/1.19  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.97/1.19  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.97/1.19  tff(c_16, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.19  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.19  tff(c_36, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.19  tff(c_44, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_20, c_36])).
% 1.97/1.19  tff(c_18, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.19  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.19  tff(c_125, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k3_subset_1(A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.19  tff(c_129, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_125])).
% 1.97/1.19  tff(c_12, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.19  tff(c_95, plain, (![A_26, C_27, B_28]: (r1_xboole_0(A_26, C_27) | ~r1_xboole_0(B_28, C_27) | ~r1_tarski(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.19  tff(c_104, plain, (![A_26, B_11, A_10]: (r1_xboole_0(A_26, B_11) | ~r1_tarski(A_26, k4_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_12, c_95])).
% 1.97/1.19  tff(c_173, plain, (![A_39]: (r1_xboole_0(A_39, '#skF_3') | ~r1_tarski(A_39, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_129, c_104])).
% 1.97/1.19  tff(c_177, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_173])).
% 1.97/1.19  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.19  tff(c_182, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_177, c_2])).
% 1.97/1.19  tff(c_185, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_182])).
% 1.97/1.19  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_185])).
% 1.97/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.19  
% 1.97/1.19  Inference rules
% 1.97/1.19  ----------------------
% 1.97/1.19  #Ref     : 0
% 1.97/1.19  #Sup     : 49
% 1.97/1.19  #Fact    : 0
% 1.97/1.19  #Define  : 0
% 1.97/1.19  #Split   : 0
% 1.97/1.19  #Chain   : 0
% 1.97/1.19  #Close   : 0
% 1.97/1.19  
% 1.97/1.19  Ordering : KBO
% 1.97/1.19  
% 1.97/1.19  Simplification rules
% 1.97/1.19  ----------------------
% 1.97/1.19  #Subsume      : 0
% 1.97/1.19  #Demod        : 4
% 1.97/1.19  #Tautology    : 21
% 1.97/1.19  #SimpNegUnit  : 1
% 1.97/1.19  #BackRed      : 0
% 1.97/1.19  
% 1.97/1.19  #Partial instantiations: 0
% 1.97/1.19  #Strategies tried      : 1
% 1.97/1.19  
% 1.97/1.19  Timing (in seconds)
% 1.97/1.19  ----------------------
% 1.97/1.19  Preprocessing        : 0.27
% 1.97/1.19  Parsing              : 0.15
% 1.97/1.19  CNF conversion       : 0.02
% 1.97/1.19  Main loop            : 0.16
% 1.97/1.19  Inferencing          : 0.06
% 1.97/1.19  Reduction            : 0.05
% 1.97/1.19  Demodulation         : 0.04
% 1.97/1.19  BG Simplification    : 0.01
% 1.97/1.19  Subsumption          : 0.03
% 1.97/1.19  Abstraction          : 0.01
% 1.97/1.19  MUC search           : 0.00
% 1.97/1.19  Cooper               : 0.00
% 1.97/1.19  Total                : 0.46
% 1.97/1.19  Index Insertion      : 0.00
% 1.97/1.19  Index Deletion       : 0.00
% 1.97/1.19  Index Matching       : 0.00
% 1.97/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
