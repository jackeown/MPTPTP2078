%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:06 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  87 expanded)
%              Number of equality atoms :   20 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_24,plain,(
    ! [A_13] : k1_subset_1(A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,
    ( k1_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_37,plain,
    ( k1_xboole_0 != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_58,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_36,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_36])).

tff(c_81,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_38])).

tff(c_18,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [A_10] : r1_tarski('#skF_2',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_18])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_58])).

tff(c_94,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_95,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_653,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = k3_subset_1(A_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_657,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_653])).

tff(c_14,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_xboole_0(A_7,C_9)
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_896,plain,(
    ! [A_79] :
      ( r1_xboole_0(A_79,'#skF_2')
      | ~ r1_tarski(A_79,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_14])).

tff(c_929,plain,(
    r1_xboole_0('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_896])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_937,plain,(
    k4_xboole_0('#skF_2','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_929,c_20])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_967,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_937,c_56])).

tff(c_978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_967])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:21:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.37  
% 2.62/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.38  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.62/1.38  
% 2.62/1.38  %Foreground sorts:
% 2.62/1.38  
% 2.62/1.38  
% 2.62/1.38  %Background operators:
% 2.62/1.38  
% 2.62/1.38  
% 2.62/1.38  %Foreground operators:
% 2.62/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.62/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.62/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.62/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.38  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.62/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.62/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.38  
% 2.62/1.39  tff(f_51, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.62/1.39  tff(f_62, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.62/1.39  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.62/1.39  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.62/1.39  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.62/1.39  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.62/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.62/1.39  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.62/1.39  tff(c_24, plain, (![A_13]: (k1_subset_1(A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.62/1.39  tff(c_30, plain, (k1_subset_1('#skF_1')!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.62/1.39  tff(c_37, plain, (k1_xboole_0!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 2.62/1.39  tff(c_58, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_37])).
% 2.62/1.39  tff(c_36, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.62/1.39  tff(c_38, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_36])).
% 2.62/1.39  tff(c_81, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_38])).
% 2.62/1.39  tff(c_18, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.62/1.39  tff(c_85, plain, (![A_10]: (r1_tarski('#skF_2', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_18])).
% 2.62/1.39  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_58])).
% 2.62/1.39  tff(c_94, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_37])).
% 2.62/1.39  tff(c_95, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_37])).
% 2.62/1.39  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.62/1.39  tff(c_653, plain, (![A_71, B_72]: (k4_xboole_0(A_71, B_72)=k3_subset_1(A_71, B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.62/1.39  tff(c_657, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_653])).
% 2.62/1.39  tff(c_14, plain, (![A_7, C_9, B_8]: (r1_xboole_0(A_7, C_9) | ~r1_tarski(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.62/1.39  tff(c_896, plain, (![A_79]: (r1_xboole_0(A_79, '#skF_2') | ~r1_tarski(A_79, k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_657, c_14])).
% 2.62/1.39  tff(c_929, plain, (r1_xboole_0('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_95, c_896])).
% 2.62/1.39  tff(c_20, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.39  tff(c_937, plain, (k4_xboole_0('#skF_2', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_929, c_20])).
% 2.62/1.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.39  tff(c_49, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.39  tff(c_56, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_49])).
% 2.62/1.39  tff(c_967, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_937, c_56])).
% 2.62/1.39  tff(c_978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_967])).
% 2.62/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.39  
% 2.62/1.39  Inference rules
% 2.62/1.39  ----------------------
% 2.62/1.39  #Ref     : 0
% 2.62/1.39  #Sup     : 222
% 2.62/1.39  #Fact    : 0
% 2.62/1.39  #Define  : 0
% 2.62/1.39  #Split   : 2
% 2.62/1.39  #Chain   : 0
% 2.62/1.39  #Close   : 0
% 2.62/1.39  
% 2.62/1.39  Ordering : KBO
% 2.62/1.39  
% 2.62/1.39  Simplification rules
% 2.62/1.39  ----------------------
% 2.62/1.39  #Subsume      : 23
% 2.62/1.39  #Demod        : 137
% 2.62/1.39  #Tautology    : 136
% 2.62/1.39  #SimpNegUnit  : 3
% 2.62/1.39  #BackRed      : 6
% 2.62/1.39  
% 2.62/1.39  #Partial instantiations: 0
% 2.62/1.39  #Strategies tried      : 1
% 2.62/1.39  
% 2.62/1.39  Timing (in seconds)
% 2.62/1.39  ----------------------
% 2.62/1.39  Preprocessing        : 0.29
% 2.62/1.39  Parsing              : 0.15
% 2.62/1.39  CNF conversion       : 0.02
% 2.62/1.39  Main loop            : 0.33
% 2.62/1.39  Inferencing          : 0.12
% 2.62/1.39  Reduction            : 0.11
% 2.62/1.39  Demodulation         : 0.08
% 2.62/1.39  BG Simplification    : 0.01
% 2.62/1.39  Subsumption          : 0.06
% 2.62/1.39  Abstraction          : 0.02
% 2.62/1.39  MUC search           : 0.00
% 2.62/1.39  Cooper               : 0.00
% 2.62/1.39  Total                : 0.64
% 2.62/1.39  Index Insertion      : 0.00
% 2.62/1.39  Index Deletion       : 0.00
% 2.62/1.39  Index Matching       : 0.00
% 2.62/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
