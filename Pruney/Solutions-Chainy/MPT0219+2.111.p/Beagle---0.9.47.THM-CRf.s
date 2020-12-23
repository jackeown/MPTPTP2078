%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:03 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),k1_tarski(B_18)) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_12])).

tff(c_8,plain,(
    ! [C_9,B_8,A_7] :
      ( C_9 = B_8
      | k2_tarski(B_8,C_9) != k1_tarski(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [A_7] :
      ( '#skF_2' = '#skF_1'
      | k1_tarski(A_7) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_67,plain,(
    ! [A_7] : k1_tarski(A_7) != k1_tarski('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_64])).

tff(c_72,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.10  
% 1.58/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.10  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.58/1.10  
% 1.58/1.10  %Foreground sorts:
% 1.58/1.10  
% 1.58/1.10  
% 1.58/1.10  %Background operators:
% 1.58/1.10  
% 1.58/1.10  
% 1.58/1.10  %Foreground operators:
% 1.58/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.58/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.58/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.58/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.58/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.58/1.10  
% 1.58/1.11  tff(f_40, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 1.58/1.11  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.58/1.11  tff(f_35, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 1.58/1.11  tff(c_10, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.58/1.11  tff(c_40, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(B_18))=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.58/1.11  tff(c_12, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.58/1.11  tff(c_46, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_12])).
% 1.58/1.11  tff(c_8, plain, (![C_9, B_8, A_7]: (C_9=B_8 | k2_tarski(B_8, C_9)!=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.58/1.11  tff(c_64, plain, (![A_7]: ('#skF_2'='#skF_1' | k1_tarski(A_7)!=k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_8])).
% 1.58/1.11  tff(c_67, plain, (![A_7]: (k1_tarski(A_7)!=k1_tarski('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_10, c_64])).
% 1.58/1.11  tff(c_72, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_67])).
% 1.58/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.11  
% 1.58/1.11  Inference rules
% 1.58/1.11  ----------------------
% 1.58/1.11  #Ref     : 1
% 1.58/1.11  #Sup     : 17
% 1.58/1.11  #Fact    : 0
% 1.58/1.11  #Define  : 0
% 1.58/1.11  #Split   : 0
% 1.58/1.11  #Chain   : 0
% 1.58/1.11  #Close   : 0
% 1.58/1.11  
% 1.58/1.11  Ordering : KBO
% 1.58/1.11  
% 1.58/1.11  Simplification rules
% 1.58/1.11  ----------------------
% 1.58/1.11  #Subsume      : 0
% 1.58/1.11  #Demod        : 0
% 1.58/1.11  #Tautology    : 10
% 1.58/1.11  #SimpNegUnit  : 1
% 1.58/1.11  #BackRed      : 0
% 1.58/1.11  
% 1.58/1.11  #Partial instantiations: 0
% 1.58/1.11  #Strategies tried      : 1
% 1.58/1.11  
% 1.58/1.11  Timing (in seconds)
% 1.58/1.11  ----------------------
% 1.58/1.11  Preprocessing        : 0.24
% 1.58/1.11  Parsing              : 0.13
% 1.58/1.11  CNF conversion       : 0.01
% 1.58/1.11  Main loop            : 0.07
% 1.58/1.11  Inferencing          : 0.03
% 1.58/1.11  Reduction            : 0.02
% 1.58/1.11  Demodulation         : 0.01
% 1.58/1.11  BG Simplification    : 0.01
% 1.58/1.11  Subsumption          : 0.01
% 1.58/1.11  Abstraction          : 0.00
% 1.58/1.11  MUC search           : 0.00
% 1.58/1.11  Cooper               : 0.00
% 1.58/1.11  Total                : 0.33
% 1.58/1.11  Index Insertion      : 0.00
% 1.58/1.11  Index Deletion       : 0.00
% 1.58/1.11  Index Matching       : 0.00
% 1.58/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
