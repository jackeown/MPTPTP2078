%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:21 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  46 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_54,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_421,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(A_76,B_77) = k3_subset_1(A_76,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_438,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_421])).

tff(c_240,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_xboole_0(A_61,k4_xboole_0(C_62,B_63))
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_974,plain,(
    ! [A_106,C_107,B_108] :
      ( k4_xboole_0(A_106,k4_xboole_0(C_107,B_108)) = A_106
      | ~ r1_tarski(A_106,B_108) ) ),
    inference(resolution,[status(thm)],[c_240,c_16])).

tff(c_1176,plain,(
    ! [A_118] :
      ( k4_xboole_0(A_118,k3_subset_1('#skF_3','#skF_5')) = A_118
      | ~ r1_tarski(A_118,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_974])).

tff(c_52,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_104,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k1_xboole_0
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_118,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_104])).

tff(c_1204,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1176,c_118])).

tff(c_1239,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1204])).

tff(c_1241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:55:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.50  
% 3.07/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.07/1.50  
% 3.07/1.50  %Foreground sorts:
% 3.07/1.50  
% 3.07/1.50  
% 3.07/1.50  %Background operators:
% 3.07/1.50  
% 3.07/1.50  
% 3.07/1.50  %Foreground operators:
% 3.07/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.07/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.07/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.07/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.07/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.07/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.50  
% 3.07/1.51  tff(f_93, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 3.07/1.51  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.07/1.51  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.07/1.51  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.07/1.51  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.07/1.51  tff(c_50, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.51  tff(c_54, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.51  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.51  tff(c_421, plain, (![A_76, B_77]: (k4_xboole_0(A_76, B_77)=k3_subset_1(A_76, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.07/1.51  tff(c_438, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_421])).
% 3.07/1.51  tff(c_240, plain, (![A_61, C_62, B_63]: (r1_xboole_0(A_61, k4_xboole_0(C_62, B_63)) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.07/1.51  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.07/1.51  tff(c_974, plain, (![A_106, C_107, B_108]: (k4_xboole_0(A_106, k4_xboole_0(C_107, B_108))=A_106 | ~r1_tarski(A_106, B_108))), inference(resolution, [status(thm)], [c_240, c_16])).
% 3.07/1.51  tff(c_1176, plain, (![A_118]: (k4_xboole_0(A_118, k3_subset_1('#skF_3', '#skF_5'))=A_118 | ~r1_tarski(A_118, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_438, c_974])).
% 3.07/1.51  tff(c_52, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.51  tff(c_104, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=k1_xboole_0 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.07/1.51  tff(c_118, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_104])).
% 3.07/1.51  tff(c_1204, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1176, c_118])).
% 3.07/1.51  tff(c_1239, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1204])).
% 3.07/1.51  tff(c_1241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1239])).
% 3.07/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.51  
% 3.07/1.51  Inference rules
% 3.07/1.51  ----------------------
% 3.07/1.51  #Ref     : 0
% 3.07/1.51  #Sup     : 293
% 3.07/1.51  #Fact    : 0
% 3.07/1.51  #Define  : 0
% 3.07/1.51  #Split   : 5
% 3.07/1.51  #Chain   : 0
% 3.07/1.51  #Close   : 0
% 3.07/1.51  
% 3.07/1.51  Ordering : KBO
% 3.07/1.51  
% 3.07/1.51  Simplification rules
% 3.07/1.51  ----------------------
% 3.07/1.51  #Subsume      : 84
% 3.07/1.51  #Demod        : 61
% 3.07/1.51  #Tautology    : 131
% 3.07/1.51  #SimpNegUnit  : 23
% 3.07/1.51  #BackRed      : 1
% 3.07/1.51  
% 3.07/1.51  #Partial instantiations: 0
% 3.07/1.51  #Strategies tried      : 1
% 3.07/1.51  
% 3.07/1.51  Timing (in seconds)
% 3.07/1.51  ----------------------
% 3.07/1.51  Preprocessing        : 0.33
% 3.07/1.52  Parsing              : 0.18
% 3.07/1.52  CNF conversion       : 0.02
% 3.07/1.52  Main loop            : 0.39
% 3.07/1.52  Inferencing          : 0.14
% 3.07/1.52  Reduction            : 0.12
% 3.07/1.52  Demodulation         : 0.08
% 3.07/1.52  BG Simplification    : 0.02
% 3.07/1.52  Subsumption          : 0.08
% 3.07/1.52  Abstraction          : 0.02
% 3.07/1.52  MUC search           : 0.00
% 3.07/1.52  Cooper               : 0.00
% 3.07/1.52  Total                : 0.75
% 3.07/1.52  Index Insertion      : 0.00
% 3.07/1.52  Index Deletion       : 0.00
% 3.07/1.52  Index Matching       : 0.00
% 3.07/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
