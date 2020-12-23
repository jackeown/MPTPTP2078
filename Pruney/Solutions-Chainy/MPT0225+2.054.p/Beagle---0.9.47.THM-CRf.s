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
% DateTime   : Thu Dec  3 09:48:37 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   41 (  62 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :    4
%              Number of atoms          :   41 (  80 expanded)
%              Number of equality atoms :   30 (  65 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(c_174,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(A_38,B_39)
      | k4_xboole_0(A_38,B_39) != A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [B_10] : ~ r1_xboole_0(k1_tarski(B_10),k1_tarski(B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_178,plain,(
    ! [B_10] : k4_xboole_0(k1_tarski(B_10),k1_tarski(B_10)) != k1_tarski(B_10) ),
    inference(resolution,[status(thm)],[c_174,c_12])).

tff(c_43,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [B_10] : k4_xboole_0(k1_tarski(B_10),k1_tarski(B_10)) != k1_tarski(B_10) ),
    inference(resolution,[status(thm)],[c_43,c_12])).

tff(c_18,plain,
    ( '#skF_2' != '#skF_1'
    | '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_23,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_53,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(k1_tarski(A_21),k1_tarski(B_22))
      | B_22 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = A_1
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(k1_tarski(A_27),k1_tarski(B_28)) = k1_tarski(A_27)
      | B_28 = A_27 ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_16,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k1_tarski('#skF_1')
    | '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_65,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_82,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_65])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23,c_82])).

tff(c_95,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_96,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_20,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_143,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_95,c_96,c_20])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_143])).

tff(c_145,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_146,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_22,plain,
    ( '#skF_2' != '#skF_1'
    | k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_198,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_145,c_146,c_22])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.21  
% 1.82/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.21  %$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.82/1.21  
% 1.82/1.21  %Foreground sorts:
% 1.82/1.21  
% 1.82/1.21  
% 1.82/1.21  %Background operators:
% 1.82/1.21  
% 1.82/1.21  
% 1.82/1.21  %Foreground operators:
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.21  
% 1.82/1.22  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.82/1.22  tff(f_40, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.82/1.22  tff(f_51, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.82/1.22  tff(f_45, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.82/1.22  tff(c_174, plain, (![A_38, B_39]: (r1_xboole_0(A_38, B_39) | k4_xboole_0(A_38, B_39)!=A_38)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.22  tff(c_12, plain, (![B_10]: (~r1_xboole_0(k1_tarski(B_10), k1_tarski(B_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.82/1.22  tff(c_178, plain, (![B_10]: (k4_xboole_0(k1_tarski(B_10), k1_tarski(B_10))!=k1_tarski(B_10))), inference(resolution, [status(thm)], [c_174, c_12])).
% 1.82/1.22  tff(c_43, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.22  tff(c_47, plain, (![B_10]: (k4_xboole_0(k1_tarski(B_10), k1_tarski(B_10))!=k1_tarski(B_10))), inference(resolution, [status(thm)], [c_43, c_12])).
% 1.82/1.22  tff(c_18, plain, ('#skF_2'!='#skF_1' | '#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.82/1.22  tff(c_23, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_18])).
% 1.82/1.22  tff(c_53, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), k1_tarski(B_22)) | B_22=A_21)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.82/1.22  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.22  tff(c_76, plain, (![A_27, B_28]: (k4_xboole_0(k1_tarski(A_27), k1_tarski(B_28))=k1_tarski(A_27) | B_28=A_27)), inference(resolution, [status(thm)], [c_53, c_2])).
% 1.82/1.22  tff(c_16, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1') | '#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.82/1.22  tff(c_65, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_16])).
% 1.82/1.22  tff(c_82, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_76, c_65])).
% 1.82/1.22  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23, c_82])).
% 1.82/1.22  tff(c_95, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_16])).
% 1.82/1.22  tff(c_96, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_16])).
% 1.82/1.22  tff(c_20, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.82/1.22  tff(c_143, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_95, c_96, c_20])).
% 1.82/1.22  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_143])).
% 1.82/1.22  tff(c_145, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_18])).
% 1.82/1.22  tff(c_146, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_18])).
% 1.82/1.22  tff(c_22, plain, ('#skF_2'!='#skF_1' | k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.82/1.22  tff(c_198, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_145, c_146, c_22])).
% 1.82/1.22  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_198])).
% 1.82/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.22  
% 1.82/1.22  Inference rules
% 1.82/1.22  ----------------------
% 1.82/1.22  #Ref     : 0
% 1.82/1.22  #Sup     : 37
% 1.82/1.22  #Fact    : 0
% 1.82/1.22  #Define  : 0
% 1.82/1.22  #Split   : 2
% 1.82/1.22  #Chain   : 0
% 1.82/1.22  #Close   : 0
% 1.82/1.22  
% 1.82/1.22  Ordering : KBO
% 1.82/1.22  
% 1.82/1.22  Simplification rules
% 1.82/1.22  ----------------------
% 1.82/1.22  #Subsume      : 3
% 1.82/1.22  #Demod        : 10
% 1.82/1.22  #Tautology    : 30
% 1.82/1.22  #SimpNegUnit  : 6
% 1.82/1.22  #BackRed      : 0
% 1.82/1.22  
% 1.82/1.22  #Partial instantiations: 0
% 1.82/1.22  #Strategies tried      : 1
% 1.82/1.22  
% 1.82/1.22  Timing (in seconds)
% 1.82/1.22  ----------------------
% 1.82/1.23  Preprocessing        : 0.26
% 1.82/1.23  Parsing              : 0.13
% 1.82/1.23  CNF conversion       : 0.02
% 1.82/1.23  Main loop            : 0.13
% 1.82/1.23  Inferencing          : 0.05
% 1.82/1.23  Reduction            : 0.03
% 1.82/1.23  Demodulation         : 0.02
% 1.82/1.23  BG Simplification    : 0.01
% 1.82/1.23  Subsumption          : 0.02
% 1.82/1.23  Abstraction          : 0.01
% 1.82/1.23  MUC search           : 0.00
% 1.82/1.23  Cooper               : 0.00
% 1.82/1.23  Total                : 0.41
% 1.82/1.23  Index Insertion      : 0.00
% 1.82/1.23  Index Deletion       : 0.00
% 1.82/1.23  Index Matching       : 0.00
% 1.82/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
