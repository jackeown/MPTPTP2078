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
% DateTime   : Thu Dec  3 09:48:38 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   48 (  53 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   36 (  45 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_62,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_66,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_70,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_40,plain,(
    ! [C_30] : r2_hidden(C_30,k1_tarski(C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_320,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_338,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_320])).

tff(c_343,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_338])).

tff(c_402,plain,(
    ! [A_90,B_91] : k4_xboole_0(A_90,k4_xboole_0(A_90,B_91)) = k3_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_428,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_402])).

tff(c_437,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_428])).

tff(c_709,plain,(
    ! [A_103,B_104] :
      ( ~ r2_hidden(A_103,B_104)
      | k4_xboole_0(k1_tarski(A_103),B_104) != k1_tarski(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_713,plain,(
    ! [A_103] :
      ( ~ r2_hidden(A_103,k1_tarski(A_103))
      | k1_tarski(A_103) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_709])).

tff(c_726,plain,(
    ! [A_103] : k1_tarski(A_103) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_713])).

tff(c_949,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(k1_tarski(A_118),B_119) = k1_tarski(A_118)
      | r2_hidden(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_72,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_984,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_949,c_72])).

tff(c_1018,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_726,c_984])).

tff(c_38,plain,(
    ! [C_30,A_26] :
      ( C_30 = A_26
      | ~ r2_hidden(C_30,k1_tarski(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1029,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1018,c_38])).

tff(c_1033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1029])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:44:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.37  
% 2.59/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.37  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 2.87/1.37  
% 2.87/1.37  %Foreground sorts:
% 2.87/1.37  
% 2.87/1.37  
% 2.87/1.37  %Background operators:
% 2.87/1.37  
% 2.87/1.37  
% 2.87/1.37  %Foreground operators:
% 2.87/1.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.87/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.87/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.87/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.87/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.87/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.87/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.87/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.87/1.37  
% 2.87/1.38  tff(f_105, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.87/1.38  tff(f_79, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.87/1.38  tff(f_62, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.87/1.38  tff(f_66, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.87/1.38  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.87/1.38  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.87/1.38  tff(f_98, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.87/1.38  tff(c_70, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.87/1.38  tff(c_40, plain, (![C_30]: (r2_hidden(C_30, k1_tarski(C_30)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.87/1.38  tff(c_26, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.38  tff(c_30, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.87/1.38  tff(c_320, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.38  tff(c_338, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_320])).
% 2.87/1.38  tff(c_343, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_338])).
% 2.87/1.38  tff(c_402, plain, (![A_90, B_91]: (k4_xboole_0(A_90, k4_xboole_0(A_90, B_91))=k3_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.38  tff(c_428, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_343, c_402])).
% 2.87/1.38  tff(c_437, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_428])).
% 2.87/1.38  tff(c_709, plain, (![A_103, B_104]: (~r2_hidden(A_103, B_104) | k4_xboole_0(k1_tarski(A_103), B_104)!=k1_tarski(A_103))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.87/1.38  tff(c_713, plain, (![A_103]: (~r2_hidden(A_103, k1_tarski(A_103)) | k1_tarski(A_103)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_437, c_709])).
% 2.87/1.38  tff(c_726, plain, (![A_103]: (k1_tarski(A_103)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_713])).
% 2.87/1.38  tff(c_949, plain, (![A_118, B_119]: (k4_xboole_0(k1_tarski(A_118), B_119)=k1_tarski(A_118) | r2_hidden(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.87/1.38  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.87/1.38  tff(c_984, plain, (k1_tarski('#skF_5')=k1_xboole_0 | r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_949, c_72])).
% 2.87/1.38  tff(c_1018, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_726, c_984])).
% 2.87/1.38  tff(c_38, plain, (![C_30, A_26]: (C_30=A_26 | ~r2_hidden(C_30, k1_tarski(A_26)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.87/1.38  tff(c_1029, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1018, c_38])).
% 2.87/1.38  tff(c_1033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1029])).
% 2.87/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.38  
% 2.87/1.38  Inference rules
% 2.87/1.38  ----------------------
% 2.87/1.38  #Ref     : 0
% 2.87/1.38  #Sup     : 226
% 2.87/1.38  #Fact    : 0
% 2.87/1.38  #Define  : 0
% 2.87/1.38  #Split   : 2
% 2.87/1.38  #Chain   : 0
% 2.87/1.38  #Close   : 0
% 2.87/1.38  
% 2.87/1.38  Ordering : KBO
% 2.87/1.38  
% 2.87/1.38  Simplification rules
% 2.87/1.38  ----------------------
% 2.87/1.38  #Subsume      : 8
% 2.87/1.38  #Demod        : 93
% 2.87/1.38  #Tautology    : 165
% 2.87/1.38  #SimpNegUnit  : 13
% 2.87/1.38  #BackRed      : 2
% 2.87/1.38  
% 2.87/1.38  #Partial instantiations: 0
% 2.87/1.38  #Strategies tried      : 1
% 2.87/1.38  
% 2.87/1.38  Timing (in seconds)
% 2.87/1.38  ----------------------
% 2.87/1.39  Preprocessing        : 0.36
% 2.87/1.39  Parsing              : 0.19
% 2.87/1.39  CNF conversion       : 0.02
% 2.87/1.39  Main loop            : 0.33
% 2.87/1.39  Inferencing          : 0.11
% 2.87/1.39  Reduction            : 0.12
% 2.87/1.39  Demodulation         : 0.09
% 2.87/1.39  BG Simplification    : 0.02
% 2.87/1.39  Subsumption          : 0.05
% 2.87/1.39  Abstraction          : 0.02
% 2.87/1.39  MUC search           : 0.00
% 2.87/1.39  Cooper               : 0.00
% 2.87/1.39  Total                : 0.71
% 2.87/1.39  Index Insertion      : 0.00
% 2.87/1.39  Index Deletion       : 0.00
% 2.87/1.39  Index Matching       : 0.00
% 2.87/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
