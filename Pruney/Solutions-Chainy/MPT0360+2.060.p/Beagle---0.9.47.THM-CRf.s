%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:26 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  53 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_41,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k3_subset_1(A_23,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_45,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_41])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_xboole_0(k4_xboole_0(A_9,B_10),B_10) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_37,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_xboole_0(A_20,C_21)
      | ~ r1_xboole_0(B_22,C_21)
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [A_25,B_26,A_27] :
      ( r1_xboole_0(A_25,B_26)
      | ~ r1_tarski(A_25,k4_xboole_0(A_27,B_26)) ) ),
    inference(resolution,[status(thm)],[c_10,c_37])).

tff(c_64,plain,(
    ! [A_28] :
      ( r1_xboole_0(A_28,'#skF_3')
      | ~ r1_tarski(A_28,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_60])).

tff(c_68,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_64])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( ~ r1_xboole_0(B_8,A_7)
      | ~ r1_tarski(B_8,A_7)
      | v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_73,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_8])).

tff(c_77,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_73])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:49:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.11  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.65/1.11  
% 1.65/1.11  %Foreground sorts:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Background operators:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Foreground operators:
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.65/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.65/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.11  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.65/1.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.65/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.65/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.11  
% 1.65/1.12  tff(f_60, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 1.65/1.12  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.65/1.12  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.65/1.12  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.65/1.12  tff(f_45, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.65/1.12  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.65/1.12  tff(c_14, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.65/1.12  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.65/1.12  tff(c_16, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.65/1.12  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.65/1.12  tff(c_41, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k3_subset_1(A_23, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.65/1.12  tff(c_45, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_41])).
% 1.65/1.12  tff(c_10, plain, (![A_9, B_10]: (r1_xboole_0(k4_xboole_0(A_9, B_10), B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.65/1.12  tff(c_37, plain, (![A_20, C_21, B_22]: (r1_xboole_0(A_20, C_21) | ~r1_xboole_0(B_22, C_21) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.65/1.12  tff(c_60, plain, (![A_25, B_26, A_27]: (r1_xboole_0(A_25, B_26) | ~r1_tarski(A_25, k4_xboole_0(A_27, B_26)))), inference(resolution, [status(thm)], [c_10, c_37])).
% 1.65/1.12  tff(c_64, plain, (![A_28]: (r1_xboole_0(A_28, '#skF_3') | ~r1_tarski(A_28, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_45, c_60])).
% 1.65/1.12  tff(c_68, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_64])).
% 1.65/1.12  tff(c_8, plain, (![B_8, A_7]: (~r1_xboole_0(B_8, A_7) | ~r1_tarski(B_8, A_7) | v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.12  tff(c_73, plain, (~r1_tarski('#skF_2', '#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_8])).
% 1.65/1.12  tff(c_77, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_73])).
% 1.65/1.12  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.12  tff(c_85, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_77, c_2])).
% 1.65/1.12  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_85])).
% 1.65/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  Inference rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Ref     : 0
% 1.65/1.12  #Sup     : 16
% 1.65/1.12  #Fact    : 0
% 1.65/1.12  #Define  : 0
% 1.65/1.12  #Split   : 0
% 1.65/1.12  #Chain   : 0
% 1.65/1.12  #Close   : 0
% 1.65/1.12  
% 1.65/1.12  Ordering : KBO
% 1.65/1.12  
% 1.65/1.12  Simplification rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Subsume      : 0
% 1.65/1.12  #Demod        : 2
% 1.65/1.12  #Tautology    : 4
% 1.65/1.12  #SimpNegUnit  : 1
% 1.65/1.12  #BackRed      : 0
% 1.65/1.12  
% 1.65/1.12  #Partial instantiations: 0
% 1.65/1.12  #Strategies tried      : 1
% 1.65/1.12  
% 1.65/1.12  Timing (in seconds)
% 1.65/1.12  ----------------------
% 1.65/1.13  Preprocessing        : 0.27
% 1.65/1.13  Parsing              : 0.14
% 1.65/1.13  CNF conversion       : 0.02
% 1.65/1.13  Main loop            : 0.10
% 1.65/1.13  Inferencing          : 0.04
% 1.65/1.13  Reduction            : 0.03
% 1.65/1.13  Demodulation         : 0.02
% 1.65/1.13  BG Simplification    : 0.01
% 1.65/1.13  Subsumption          : 0.01
% 1.65/1.13  Abstraction          : 0.00
% 1.65/1.13  MUC search           : 0.00
% 1.65/1.13  Cooper               : 0.00
% 1.65/1.13  Total                : 0.40
% 1.65/1.13  Index Insertion      : 0.00
% 1.76/1.13  Index Deletion       : 0.00
% 1.76/1.13  Index Matching       : 0.00
% 1.76/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
