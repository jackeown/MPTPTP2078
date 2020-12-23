%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:06 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 211 expanded)
%              Number of leaves         :   23 (  84 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 ( 264 expanded)
%              Number of equality atoms :   15 ( 128 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_63,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_41,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_40,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(c_36,plain,(
    ! [A_35] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_223,plain,(
    ! [B_70,A_71] :
      ( m1_subset_1(k1_tarski(B_70),k1_zfmisc_1(A_71))
      | k1_xboole_0 = A_71
      | ~ m1_subset_1(B_70,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_228,plain,
    ( k1_zfmisc_1('#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_223,c_42])).

tff(c_235,plain,(
    k1_zfmisc_1('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_228])).

tff(c_32,plain,(
    ! [A_26] : k3_tarski(k1_zfmisc_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_247,plain,(
    k3_tarski(k1_xboole_0) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_32])).

tff(c_16,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_253,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_16])).

tff(c_249,plain,(
    m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_36])).

tff(c_281,plain,(
    m1_subset_1('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_249])).

tff(c_260,plain,(
    k1_zfmisc_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_235])).

tff(c_14,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_275,plain,(
    k1_zfmisc_1('#skF_2') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_14])).

tff(c_304,plain,(
    k1_tarski('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_275])).

tff(c_237,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_42])).

tff(c_238,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_237])).

tff(c_258,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'),k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_253,c_238])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_304,c_304,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:31:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.65  
% 2.48/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.65  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2
% 2.67/1.65  
% 2.67/1.65  %Foreground sorts:
% 2.67/1.65  
% 2.67/1.65  
% 2.67/1.65  %Background operators:
% 2.67/1.65  
% 2.67/1.65  
% 2.67/1.65  %Foreground operators:
% 2.67/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.67/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.65  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.65  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.67/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.65  
% 2.67/1.66  tff(f_68, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.67/1.66  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.67/1.66  tff(f_84, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 2.67/1.66  tff(f_63, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.67/1.66  tff(f_41, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.67/1.66  tff(f_40, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.67/1.66  tff(c_36, plain, (![A_35]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.67/1.66  tff(c_223, plain, (![B_70, A_71]: (m1_subset_1(k1_tarski(B_70), k1_zfmisc_1(A_71)) | k1_xboole_0=A_71 | ~m1_subset_1(B_70, A_71))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.67/1.66  tff(c_42, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.67/1.66  tff(c_228, plain, (k1_zfmisc_1('#skF_2')=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_223, c_42])).
% 2.67/1.66  tff(c_235, plain, (k1_zfmisc_1('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_228])).
% 2.67/1.66  tff(c_32, plain, (![A_26]: (k3_tarski(k1_zfmisc_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.67/1.66  tff(c_247, plain, (k3_tarski(k1_xboole_0)='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_235, c_32])).
% 2.67/1.66  tff(c_16, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.67/1.66  tff(c_253, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_16])).
% 2.67/1.66  tff(c_249, plain, (m1_subset_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_235, c_36])).
% 2.67/1.66  tff(c_281, plain, (m1_subset_1('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_249])).
% 2.67/1.66  tff(c_260, plain, (k1_zfmisc_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_253, c_235])).
% 2.67/1.66  tff(c_14, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.66  tff(c_275, plain, (k1_zfmisc_1('#skF_2')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_14])).
% 2.67/1.66  tff(c_304, plain, (k1_tarski('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_260, c_275])).
% 2.67/1.66  tff(c_237, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_42])).
% 2.67/1.66  tff(c_238, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_237])).
% 2.67/1.66  tff(c_258, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_253, c_238])).
% 2.67/1.66  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_304, c_304, c_258])).
% 2.67/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.66  
% 2.67/1.66  Inference rules
% 2.67/1.66  ----------------------
% 2.67/1.66  #Ref     : 0
% 2.67/1.66  #Sup     : 74
% 2.67/1.66  #Fact    : 0
% 2.67/1.66  #Define  : 0
% 2.67/1.66  #Split   : 0
% 2.67/1.66  #Chain   : 0
% 2.67/1.66  #Close   : 0
% 2.67/1.66  
% 2.67/1.66  Ordering : KBO
% 2.67/1.66  
% 2.67/1.66  Simplification rules
% 2.67/1.66  ----------------------
% 2.67/1.66  #Subsume      : 3
% 2.67/1.66  #Demod        : 43
% 2.67/1.66  #Tautology    : 52
% 2.67/1.66  #SimpNegUnit  : 2
% 2.67/1.66  #BackRed      : 21
% 2.67/1.66  
% 2.67/1.66  #Partial instantiations: 0
% 2.67/1.66  #Strategies tried      : 1
% 2.67/1.66  
% 2.67/1.66  Timing (in seconds)
% 2.67/1.66  ----------------------
% 2.67/1.66  Preprocessing        : 0.53
% 2.67/1.66  Parsing              : 0.27
% 2.67/1.66  CNF conversion       : 0.03
% 2.67/1.66  Main loop            : 0.28
% 2.67/1.66  Inferencing          : 0.10
% 2.67/1.66  Reduction            : 0.09
% 2.67/1.66  Demodulation         : 0.07
% 2.67/1.66  BG Simplification    : 0.02
% 2.67/1.66  Subsumption          : 0.04
% 2.67/1.66  Abstraction          : 0.02
% 2.67/1.66  MUC search           : 0.00
% 2.67/1.66  Cooper               : 0.00
% 2.67/1.66  Total                : 0.84
% 2.67/1.66  Index Insertion      : 0.00
% 2.67/1.67  Index Deletion       : 0.00
% 2.67/1.67  Index Matching       : 0.00
% 2.67/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
