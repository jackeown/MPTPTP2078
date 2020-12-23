%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:15 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   44 (  59 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  68 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_26,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_206,plain,(
    ! [B_38,A_39] :
      ( k1_tarski(B_38) = A_39
      | k1_xboole_0 = A_39
      | ~ r1_tarski(A_39,k1_tarski(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_217,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_206])).

tff(c_231,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_tarski(k1_tarski(A_18),k2_tarski(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_241,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_22])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_257,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_241,c_4])).

tff(c_79,plain,(
    ! [A_29,B_30] :
      ( k2_xboole_0(A_29,B_30) = B_30
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_31] : k2_xboole_0(k1_xboole_0,A_31) = A_31 ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_102,plain,(
    ! [A_31] : k2_xboole_0(A_31,k1_xboole_0) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_2])).

tff(c_261,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_102])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( B_21 = A_20
      | ~ r1_tarski(k1_tarski(A_20),k1_tarski(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_296,plain,(
    ! [B_21] :
      ( B_21 = '#skF_1'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(B_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_24])).

tff(c_321,plain,(
    ! [B_47] : B_47 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_296])).

tff(c_373,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_26])).

tff(c_374,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_386,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_22])).

tff(c_395,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_386,c_24])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.65  
% 2.68/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.66  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.68/1.66  
% 2.68/1.66  %Foreground sorts:
% 2.68/1.66  
% 2.68/1.66  
% 2.68/1.66  %Background operators:
% 2.68/1.66  
% 2.68/1.66  
% 2.68/1.66  %Foreground operators:
% 2.68/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.66  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.66  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.66  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.68/1.66  
% 2.73/1.67  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.73/1.67  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.73/1.67  tff(f_47, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.73/1.67  tff(f_49, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.73/1.67  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.73/1.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.73/1.67  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.73/1.67  tff(c_26, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.67  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.73/1.67  tff(c_28, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.67  tff(c_206, plain, (![B_38, A_39]: (k1_tarski(B_38)=A_39 | k1_xboole_0=A_39 | ~r1_tarski(A_39, k1_tarski(B_38)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.73/1.67  tff(c_217, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_206])).
% 2.73/1.67  tff(c_231, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_217])).
% 2.73/1.67  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(k1_tarski(A_18), k2_tarski(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.67  tff(c_241, plain, (r1_tarski(k1_tarski('#skF_1'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_231, c_22])).
% 2.73/1.67  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.67  tff(c_257, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_241, c_4])).
% 2.73/1.67  tff(c_79, plain, (![A_29, B_30]: (k2_xboole_0(A_29, B_30)=B_30 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.67  tff(c_96, plain, (![A_31]: (k2_xboole_0(k1_xboole_0, A_31)=A_31)), inference(resolution, [status(thm)], [c_6, c_79])).
% 2.73/1.67  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.73/1.67  tff(c_102, plain, (![A_31]: (k2_xboole_0(A_31, k1_xboole_0)=A_31)), inference(superposition, [status(thm), theory('equality')], [c_96, c_2])).
% 2.73/1.67  tff(c_261, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_257, c_102])).
% 2.73/1.67  tff(c_24, plain, (![B_21, A_20]: (B_21=A_20 | ~r1_tarski(k1_tarski(A_20), k1_tarski(B_21)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.67  tff(c_296, plain, (![B_21]: (B_21='#skF_1' | ~r1_tarski(k1_xboole_0, k1_tarski(B_21)))), inference(superposition, [status(thm), theory('equality')], [c_261, c_24])).
% 2.73/1.67  tff(c_321, plain, (![B_47]: (B_47='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_296])).
% 2.73/1.67  tff(c_373, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_321, c_26])).
% 2.73/1.67  tff(c_374, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_217])).
% 2.73/1.67  tff(c_386, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_374, c_22])).
% 2.73/1.67  tff(c_395, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_386, c_24])).
% 2.73/1.67  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_395])).
% 2.73/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.67  
% 2.73/1.67  Inference rules
% 2.73/1.67  ----------------------
% 2.73/1.67  #Ref     : 0
% 2.73/1.67  #Sup     : 102
% 2.73/1.67  #Fact    : 0
% 2.73/1.67  #Define  : 0
% 2.73/1.67  #Split   : 1
% 2.73/1.67  #Chain   : 0
% 2.73/1.67  #Close   : 0
% 2.73/1.67  
% 2.73/1.67  Ordering : KBO
% 2.73/1.67  
% 2.73/1.67  Simplification rules
% 2.73/1.67  ----------------------
% 2.73/1.67  #Subsume      : 11
% 2.73/1.67  #Demod        : 38
% 2.73/1.67  #Tautology    : 65
% 2.73/1.67  #SimpNegUnit  : 1
% 2.73/1.67  #BackRed      : 9
% 2.73/1.67  
% 2.73/1.67  #Partial instantiations: 0
% 2.73/1.67  #Strategies tried      : 1
% 2.73/1.67  
% 2.73/1.67  Timing (in seconds)
% 2.73/1.67  ----------------------
% 2.73/1.68  Preprocessing        : 0.49
% 2.73/1.68  Parsing              : 0.25
% 2.73/1.68  CNF conversion       : 0.03
% 2.73/1.68  Main loop            : 0.36
% 2.73/1.68  Inferencing          : 0.13
% 2.73/1.68  Reduction            : 0.12
% 2.73/1.68  Demodulation         : 0.09
% 2.73/1.68  BG Simplification    : 0.03
% 2.73/1.68  Subsumption          : 0.06
% 2.73/1.68  Abstraction          : 0.02
% 2.73/1.68  MUC search           : 0.00
% 2.73/1.68  Cooper               : 0.00
% 2.73/1.68  Total                : 0.89
% 2.73/1.68  Index Insertion      : 0.00
% 2.73/1.68  Index Deletion       : 0.00
% 2.73/1.68  Index Matching       : 0.00
% 2.73/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
