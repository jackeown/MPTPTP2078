%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:33 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   17 (  20 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  16 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(A,B) = k1_xboole_0
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(c_6,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_22])).

tff(c_45,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2,c_37])).

tff(c_47,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:22:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.07  
% 1.55/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.07  %$ k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.58/1.07  
% 1.58/1.07  %Foreground sorts:
% 1.58/1.07  
% 1.58/1.07  
% 1.58/1.07  %Background operators:
% 1.58/1.07  
% 1.58/1.07  
% 1.58/1.07  %Foreground operators:
% 1.58/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.58/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.58/1.07  
% 1.58/1.08  tff(f_34, negated_conjecture, ~(![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.58/1.08  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.58/1.08  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 1.58/1.08  tff(c_6, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.08  tff(c_8, plain, (k2_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.08  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.58/1.08  tff(c_22, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.08  tff(c_37, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8, c_22])).
% 1.58/1.08  tff(c_45, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2, c_37])).
% 1.58/1.08  tff(c_47, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_45])).
% 1.58/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.08  
% 1.58/1.08  Inference rules
% 1.58/1.08  ----------------------
% 1.58/1.08  #Ref     : 0
% 1.58/1.08  #Sup     : 10
% 1.58/1.08  #Fact    : 0
% 1.58/1.08  #Define  : 0
% 1.58/1.08  #Split   : 0
% 1.58/1.08  #Chain   : 0
% 1.58/1.08  #Close   : 0
% 1.58/1.08  
% 1.58/1.08  Ordering : KBO
% 1.58/1.08  
% 1.58/1.08  Simplification rules
% 1.58/1.08  ----------------------
% 1.58/1.08  #Subsume      : 0
% 1.58/1.08  #Demod        : 6
% 1.58/1.08  #Tautology    : 8
% 1.58/1.08  #SimpNegUnit  : 1
% 1.58/1.08  #BackRed      : 0
% 1.58/1.08  
% 1.58/1.08  #Partial instantiations: 0
% 1.58/1.08  #Strategies tried      : 1
% 1.58/1.08  
% 1.58/1.08  Timing (in seconds)
% 1.58/1.08  ----------------------
% 1.58/1.08  Preprocessing        : 0.25
% 1.58/1.08  Parsing              : 0.13
% 1.58/1.08  CNF conversion       : 0.01
% 1.58/1.08  Main loop            : 0.07
% 1.58/1.08  Inferencing          : 0.03
% 1.58/1.08  Reduction            : 0.02
% 1.58/1.08  Demodulation         : 0.02
% 1.58/1.08  BG Simplification    : 0.01
% 1.58/1.08  Subsumption          : 0.01
% 1.58/1.08  Abstraction          : 0.00
% 1.58/1.08  MUC search           : 0.00
% 1.58/1.08  Cooper               : 0.00
% 1.58/1.08  Total                : 0.34
% 1.58/1.08  Index Insertion      : 0.00
% 1.58/1.08  Index Deletion       : 0.00
% 1.58/1.08  Index Matching       : 0.00
% 1.58/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
