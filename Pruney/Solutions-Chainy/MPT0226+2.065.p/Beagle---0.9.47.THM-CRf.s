%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:45 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   45 (  47 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  38 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_48,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    ! [B_40,A_41] :
      ( r1_xboole_0(B_40,A_41)
      | ~ r1_xboole_0(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    ! [A_10] : r1_xboole_0(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_14,c_81])).

tff(c_101,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = A_47
      | ~ r1_xboole_0(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_112,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_101])).

tff(c_270,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k4_xboole_0(B_71,A_70)) = k2_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_279,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k2_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_270])).

tff(c_294,plain,(
    ! [A_72] : k2_xboole_0(A_72,k1_xboole_0) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_279])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_300,plain,(
    ! [A_72] : k4_xboole_0(A_72,A_72) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_10])).

tff(c_44,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_306,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_44])).

tff(c_530,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(k1_tarski(A_82),k1_tarski(B_83)) = k1_tarski(A_82)
      | B_83 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_50,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_549,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_50])).

tff(c_569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_306,c_549])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.27  
% 2.02/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.28  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.02/1.28  
% 2.02/1.28  %Foreground sorts:
% 2.02/1.28  
% 2.02/1.28  
% 2.02/1.28  %Background operators:
% 2.02/1.28  
% 2.02/1.28  
% 2.02/1.28  %Foreground operators:
% 2.02/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.02/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.02/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.28  
% 2.33/1.29  tff(f_77, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.33/1.29  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.33/1.29  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.33/1.29  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.33/1.29  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.33/1.29  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.33/1.29  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.33/1.29  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.33/1.29  tff(c_48, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.33/1.29  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.29  tff(c_14, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.29  tff(c_81, plain, (![B_40, A_41]: (r1_xboole_0(B_40, A_41) | ~r1_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.33/1.29  tff(c_84, plain, (![A_10]: (r1_xboole_0(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_14, c_81])).
% 2.33/1.29  tff(c_101, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=A_47 | ~r1_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.33/1.29  tff(c_112, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_101])).
% 2.33/1.29  tff(c_270, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k4_xboole_0(B_71, A_70))=k2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.33/1.29  tff(c_279, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k2_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_112, c_270])).
% 2.33/1.29  tff(c_294, plain, (![A_72]: (k2_xboole_0(A_72, k1_xboole_0)=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_279])).
% 2.33/1.29  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.33/1.29  tff(c_300, plain, (![A_72]: (k4_xboole_0(A_72, A_72)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_294, c_10])).
% 2.33/1.29  tff(c_44, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.33/1.29  tff(c_306, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_300, c_44])).
% 2.33/1.29  tff(c_530, plain, (![A_82, B_83]: (k4_xboole_0(k1_tarski(A_82), k1_tarski(B_83))=k1_tarski(A_82) | B_83=A_82)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.33/1.29  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.33/1.29  tff(c_549, plain, (k1_tarski('#skF_3')=k1_xboole_0 | '#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_530, c_50])).
% 2.33/1.29  tff(c_569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_306, c_549])).
% 2.33/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.29  
% 2.33/1.29  Inference rules
% 2.33/1.29  ----------------------
% 2.33/1.29  #Ref     : 0
% 2.33/1.29  #Sup     : 121
% 2.33/1.29  #Fact    : 0
% 2.33/1.29  #Define  : 0
% 2.33/1.29  #Split   : 0
% 2.33/1.29  #Chain   : 0
% 2.33/1.29  #Close   : 0
% 2.33/1.29  
% 2.33/1.29  Ordering : KBO
% 2.33/1.29  
% 2.33/1.29  Simplification rules
% 2.33/1.29  ----------------------
% 2.33/1.29  #Subsume      : 4
% 2.33/1.29  #Demod        : 30
% 2.33/1.29  #Tautology    : 77
% 2.33/1.29  #SimpNegUnit  : 4
% 2.33/1.29  #BackRed      : 1
% 2.33/1.29  
% 2.33/1.29  #Partial instantiations: 0
% 2.33/1.29  #Strategies tried      : 1
% 2.33/1.29  
% 2.33/1.29  Timing (in seconds)
% 2.33/1.29  ----------------------
% 2.33/1.29  Preprocessing        : 0.31
% 2.33/1.29  Parsing              : 0.16
% 2.33/1.29  CNF conversion       : 0.02
% 2.33/1.29  Main loop            : 0.23
% 2.33/1.29  Inferencing          : 0.09
% 2.33/1.29  Reduction            : 0.07
% 2.33/1.29  Demodulation         : 0.05
% 2.33/1.29  BG Simplification    : 0.02
% 2.33/1.29  Subsumption          : 0.04
% 2.33/1.29  Abstraction          : 0.01
% 2.33/1.29  MUC search           : 0.00
% 2.33/1.29  Cooper               : 0.00
% 2.33/1.29  Total                : 0.57
% 2.33/1.29  Index Insertion      : 0.00
% 2.33/1.29  Index Deletion       : 0.00
% 2.33/1.29  Index Matching       : 0.00
% 2.33/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
