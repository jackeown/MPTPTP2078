%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:28 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  43 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_8,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k3_subset_1(A_10,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_16])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_xboole_0(k4_xboole_0(A_4,B_5),B_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4])).

tff(c_28,plain,(
    ! [A_12,B_13,C_14] :
      ( k1_xboole_0 = A_12
      | ~ r1_xboole_0(B_13,C_14)
      | ~ r1_tarski(A_12,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,'#skF_3')
      | ~ r1_tarski(A_15,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_24,c_28])).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_35])).

tff(c_41,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38])).

tff(c_43,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.13  
% 1.61/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.13  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.61/1.13  
% 1.61/1.13  %Foreground sorts:
% 1.61/1.13  
% 1.61/1.13  
% 1.61/1.13  %Background operators:
% 1.61/1.13  
% 1.61/1.13  
% 1.61/1.13  %Foreground operators:
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.61/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.13  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.61/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.61/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.61/1.13  
% 1.72/1.14  tff(f_48, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 1.72/1.14  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.72/1.14  tff(f_35, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.72/1.14  tff(f_33, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.72/1.14  tff(c_8, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.72/1.14  tff(c_12, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.72/1.14  tff(c_10, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.72/1.14  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.72/1.14  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k3_subset_1(A_10, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.14  tff(c_20, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_16])).
% 1.72/1.14  tff(c_4, plain, (![A_4, B_5]: (r1_xboole_0(k4_xboole_0(A_4, B_5), B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.14  tff(c_24, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_4])).
% 1.72/1.14  tff(c_28, plain, (![A_12, B_13, C_14]: (k1_xboole_0=A_12 | ~r1_xboole_0(B_13, C_14) | ~r1_tarski(A_12, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.72/1.14  tff(c_35, plain, (![A_15]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, '#skF_3') | ~r1_tarski(A_15, k3_subset_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_24, c_28])).
% 1.72/1.14  tff(c_38, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_35])).
% 1.72/1.14  tff(c_41, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 1.72/1.14  tff(c_43, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_41])).
% 1.72/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.14  
% 1.72/1.14  Inference rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Ref     : 0
% 1.72/1.14  #Sup     : 7
% 1.72/1.14  #Fact    : 0
% 1.72/1.14  #Define  : 0
% 1.72/1.14  #Split   : 0
% 1.72/1.14  #Chain   : 0
% 1.72/1.14  #Close   : 0
% 1.72/1.14  
% 1.72/1.14  Ordering : KBO
% 1.72/1.14  
% 1.72/1.14  Simplification rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Subsume      : 0
% 1.72/1.14  #Demod        : 1
% 1.72/1.14  #Tautology    : 2
% 1.72/1.14  #SimpNegUnit  : 1
% 1.72/1.14  #BackRed      : 0
% 1.72/1.14  
% 1.72/1.14  #Partial instantiations: 0
% 1.72/1.14  #Strategies tried      : 1
% 1.72/1.14  
% 1.72/1.14  Timing (in seconds)
% 1.72/1.14  ----------------------
% 1.72/1.14  Preprocessing        : 0.28
% 1.72/1.14  Parsing              : 0.15
% 1.72/1.14  CNF conversion       : 0.02
% 1.72/1.14  Main loop            : 0.07
% 1.72/1.14  Inferencing          : 0.03
% 1.72/1.14  Reduction            : 0.02
% 1.72/1.14  Demodulation         : 0.02
% 1.72/1.14  BG Simplification    : 0.01
% 1.72/1.14  Subsumption          : 0.01
% 1.72/1.14  Abstraction          : 0.00
% 1.72/1.14  MUC search           : 0.00
% 1.72/1.14  Cooper               : 0.00
% 1.72/1.14  Total                : 0.38
% 1.72/1.14  Index Insertion      : 0.00
% 1.72/1.15  Index Deletion       : 0.00
% 1.72/1.15  Index Matching       : 0.00
% 1.72/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
