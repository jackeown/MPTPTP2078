%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:40 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  15 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_36,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_6,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_18])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4])).

tff(c_30,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:06:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.38/0.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.38/1.00  
% 1.38/1.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.38/1.00  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.38/1.00  
% 1.38/1.00  %Foreground sorts:
% 1.38/1.00  
% 1.38/1.00  
% 1.38/1.00  %Background operators:
% 1.38/1.00  
% 1.38/1.00  
% 1.38/1.00  %Foreground operators:
% 1.38/1.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.38/1.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.38/1.00  tff('#skF_2', type, '#skF_2': $i).
% 1.38/1.00  tff('#skF_1', type, '#skF_1': $i).
% 1.38/1.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.38/1.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.38/1.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.38/1.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.38/1.00  
% 1.38/1.01  tff(f_36, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.38/1.01  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.38/1.01  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.38/1.01  tff(c_6, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.38/1.01  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.38/1.01  tff(c_18, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.38/1.01  tff(c_22, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_8, c_18])).
% 1.38/1.01  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.38/1.01  tff(c_26, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_22, c_4])).
% 1.38/1.01  tff(c_30, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_26])).
% 1.38/1.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.38/1.01  
% 1.38/1.01  Inference rules
% 1.38/1.01  ----------------------
% 1.38/1.01  #Ref     : 0
% 1.38/1.01  #Sup     : 6
% 1.38/1.01  #Fact    : 0
% 1.38/1.01  #Define  : 0
% 1.38/1.01  #Split   : 0
% 1.38/1.01  #Chain   : 0
% 1.38/1.01  #Close   : 0
% 1.38/1.01  
% 1.38/1.01  Ordering : KBO
% 1.38/1.01  
% 1.38/1.01  Simplification rules
% 1.38/1.01  ----------------------
% 1.38/1.01  #Subsume      : 0
% 1.38/1.01  #Demod        : 0
% 1.38/1.01  #Tautology    : 3
% 1.38/1.01  #SimpNegUnit  : 1
% 1.38/1.01  #BackRed      : 0
% 1.38/1.01  
% 1.38/1.01  #Partial instantiations: 0
% 1.38/1.01  #Strategies tried      : 1
% 1.38/1.01  
% 1.38/1.01  Timing (in seconds)
% 1.38/1.01  ----------------------
% 1.51/1.01  Preprocessing        : 0.22
% 1.51/1.01  Parsing              : 0.12
% 1.51/1.01  CNF conversion       : 0.01
% 1.51/1.01  Main loop            : 0.06
% 1.51/1.01  Inferencing          : 0.03
% 1.51/1.01  Reduction            : 0.02
% 1.51/1.01  Demodulation         : 0.01
% 1.51/1.01  BG Simplification    : 0.01
% 1.51/1.01  Subsumption          : 0.00
% 1.51/1.01  Abstraction          : 0.00
% 1.51/1.01  MUC search           : 0.00
% 1.51/1.01  Cooper               : 0.00
% 1.51/1.01  Total                : 0.30
% 1.51/1.01  Index Insertion      : 0.00
% 1.51/1.01  Index Deletion       : 0.00
% 1.51/1.01  Index Matching       : 0.00
% 1.51/1.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
