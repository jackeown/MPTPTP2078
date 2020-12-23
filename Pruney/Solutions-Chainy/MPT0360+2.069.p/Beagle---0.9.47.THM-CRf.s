%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:27 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  56 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(C,B)
     => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k3_subset_1(A_27,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_62,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_58])).

tff(c_75,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_xboole_0(k4_xboole_0(A_29,B_30),k3_xboole_0(A_29,k4_xboole_0(B_30,C_31))) = k4_xboole_0(A_29,C_31)
      | ~ r1_tarski(C_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_21,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(A_17,C_18)
      | ~ r1_tarski(B_19,C_18)
      | ~ r1_tarski(A_17,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_17,A_9,B_10] :
      ( r1_tarski(A_17,k2_xboole_0(A_9,B_10))
      | ~ r1_tarski(A_17,A_9) ) ),
    inference(resolution,[status(thm)],[c_8,c_21])).

tff(c_302,plain,(
    ! [A_63,A_64,C_65,B_66] :
      ( r1_tarski(A_63,k4_xboole_0(A_64,C_65))
      | ~ r1_tarski(A_63,k4_xboole_0(A_64,B_66))
      | ~ r1_tarski(C_65,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_28])).

tff(c_711,plain,(
    ! [A_107,C_108] :
      ( r1_tarski(A_107,k4_xboole_0('#skF_1',C_108))
      | ~ r1_tarski(A_107,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(C_108,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_302])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_759,plain,(
    ! [C_109] :
      ( k1_xboole_0 = C_109
      | ~ r1_tarski(C_109,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(C_109,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_711,c_6])).

tff(c_768,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_759])).

tff(c_773,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_768])).

tff(c_775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:39:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.45  
% 2.75/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.45  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.75/1.45  
% 2.75/1.45  %Foreground sorts:
% 2.75/1.45  
% 2.75/1.45  
% 2.75/1.45  %Background operators:
% 2.75/1.45  
% 2.75/1.45  
% 2.75/1.45  %Foreground operators:
% 2.75/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.75/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.75/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.45  
% 2.75/1.46  tff(f_54, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 2.75/1.46  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.75/1.46  tff(f_29, axiom, (![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 2.75/1.46  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.75/1.46  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.75/1.46  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.75/1.46  tff(c_12, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.75/1.46  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.75/1.46  tff(c_14, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.75/1.46  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.75/1.46  tff(c_58, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k3_subset_1(A_27, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.75/1.46  tff(c_62, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_58])).
% 2.75/1.46  tff(c_75, plain, (![A_29, B_30, C_31]: (k2_xboole_0(k4_xboole_0(A_29, B_30), k3_xboole_0(A_29, k4_xboole_0(B_30, C_31)))=k4_xboole_0(A_29, C_31) | ~r1_tarski(C_31, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.46  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.46  tff(c_21, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, C_18) | ~r1_tarski(B_19, C_18) | ~r1_tarski(A_17, B_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.75/1.46  tff(c_28, plain, (![A_17, A_9, B_10]: (r1_tarski(A_17, k2_xboole_0(A_9, B_10)) | ~r1_tarski(A_17, A_9))), inference(resolution, [status(thm)], [c_8, c_21])).
% 2.75/1.46  tff(c_302, plain, (![A_63, A_64, C_65, B_66]: (r1_tarski(A_63, k4_xboole_0(A_64, C_65)) | ~r1_tarski(A_63, k4_xboole_0(A_64, B_66)) | ~r1_tarski(C_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_75, c_28])).
% 2.75/1.46  tff(c_711, plain, (![A_107, C_108]: (r1_tarski(A_107, k4_xboole_0('#skF_1', C_108)) | ~r1_tarski(A_107, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(C_108, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_302])).
% 2.75/1.46  tff(c_6, plain, (![A_7, B_8]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k4_xboole_0(B_8, A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.46  tff(c_759, plain, (![C_109]: (k1_xboole_0=C_109 | ~r1_tarski(C_109, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(C_109, '#skF_3'))), inference(resolution, [status(thm)], [c_711, c_6])).
% 2.75/1.46  tff(c_768, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_759])).
% 2.75/1.46  tff(c_773, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_768])).
% 2.75/1.46  tff(c_775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_773])).
% 2.75/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.46  
% 2.75/1.46  Inference rules
% 2.75/1.46  ----------------------
% 3.10/1.46  #Ref     : 0
% 3.10/1.46  #Sup     : 211
% 3.10/1.46  #Fact    : 0
% 3.10/1.46  #Define  : 0
% 3.10/1.46  #Split   : 5
% 3.10/1.46  #Chain   : 0
% 3.10/1.46  #Close   : 0
% 3.10/1.46  
% 3.10/1.46  Ordering : KBO
% 3.10/1.46  
% 3.10/1.46  Simplification rules
% 3.10/1.46  ----------------------
% 3.10/1.46  #Subsume      : 35
% 3.10/1.46  #Demod        : 12
% 3.10/1.46  #Tautology    : 17
% 3.10/1.46  #SimpNegUnit  : 2
% 3.10/1.46  #BackRed      : 0
% 3.10/1.46  
% 3.10/1.46  #Partial instantiations: 0
% 3.10/1.46  #Strategies tried      : 1
% 3.10/1.46  
% 3.10/1.46  Timing (in seconds)
% 3.10/1.46  ----------------------
% 3.10/1.47  Preprocessing        : 0.28
% 3.10/1.47  Parsing              : 0.16
% 3.10/1.47  CNF conversion       : 0.02
% 3.10/1.47  Main loop            : 0.40
% 3.10/1.47  Inferencing          : 0.14
% 3.10/1.47  Reduction            : 0.11
% 3.10/1.47  Demodulation         : 0.08
% 3.10/1.47  BG Simplification    : 0.02
% 3.10/1.47  Subsumption          : 0.10
% 3.10/1.47  Abstraction          : 0.02
% 3.10/1.47  MUC search           : 0.00
% 3.10/1.47  Cooper               : 0.00
% 3.10/1.47  Total                : 0.71
% 3.10/1.47  Index Insertion      : 0.00
% 3.10/1.47  Index Deletion       : 0.00
% 3.10/1.47  Index Matching       : 0.00
% 3.10/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
