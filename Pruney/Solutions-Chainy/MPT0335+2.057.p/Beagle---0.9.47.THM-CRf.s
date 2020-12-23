%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:00 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  37 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_8,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_37,plain,(
    ! [A_12,B_13,C_14] : k3_xboole_0(k3_xboole_0(A_12,B_13),C_14) = k3_xboole_0(A_12,k3_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_71,plain,(
    ! [C_15] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_15)) = k3_xboole_0('#skF_1',C_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_37])).

tff(c_87,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_71])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k3_xboole_0(B_7,k1_tarski(A_6)) = k1_tarski(A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_6])).

tff(c_106,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_98])).

tff(c_108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.13  
% 1.60/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.13  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.60/1.13  
% 1.60/1.13  %Foreground sorts:
% 1.60/1.13  
% 1.60/1.13  
% 1.60/1.13  %Background operators:
% 1.60/1.13  
% 1.60/1.13  
% 1.60/1.13  %Foreground operators:
% 1.60/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.60/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.60/1.13  
% 1.60/1.14  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 1.60/1.14  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.60/1.14  tff(f_27, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.60/1.14  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.60/1.14  tff(c_8, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.60/1.14  tff(c_10, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.60/1.14  tff(c_12, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.60/1.14  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.60/1.14  tff(c_19, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.14  tff(c_23, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_14, c_19])).
% 1.60/1.14  tff(c_37, plain, (![A_12, B_13, C_14]: (k3_xboole_0(k3_xboole_0(A_12, B_13), C_14)=k3_xboole_0(A_12, k3_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.14  tff(c_71, plain, (![C_15]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_15))=k3_xboole_0('#skF_1', C_15))), inference(superposition, [status(thm), theory('equality')], [c_23, c_37])).
% 1.60/1.14  tff(c_87, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_71])).
% 1.60/1.14  tff(c_6, plain, (![B_7, A_6]: (k3_xboole_0(B_7, k1_tarski(A_6))=k1_tarski(A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.60/1.14  tff(c_98, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_87, c_6])).
% 1.60/1.14  tff(c_106, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_98])).
% 1.60/1.14  tff(c_108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_106])).
% 1.60/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.14  
% 1.60/1.14  Inference rules
% 1.60/1.14  ----------------------
% 1.60/1.14  #Ref     : 0
% 1.60/1.14  #Sup     : 26
% 1.60/1.14  #Fact    : 0
% 1.60/1.14  #Define  : 0
% 1.60/1.14  #Split   : 0
% 1.60/1.14  #Chain   : 0
% 1.60/1.14  #Close   : 0
% 1.60/1.14  
% 1.60/1.14  Ordering : KBO
% 1.60/1.14  
% 1.60/1.14  Simplification rules
% 1.60/1.14  ----------------------
% 1.60/1.14  #Subsume      : 0
% 1.60/1.14  #Demod        : 11
% 1.60/1.14  #Tautology    : 15
% 1.60/1.14  #SimpNegUnit  : 1
% 1.60/1.14  #BackRed      : 0
% 1.60/1.14  
% 1.60/1.14  #Partial instantiations: 0
% 1.60/1.14  #Strategies tried      : 1
% 1.60/1.14  
% 1.60/1.14  Timing (in seconds)
% 1.60/1.14  ----------------------
% 1.60/1.14  Preprocessing        : 0.26
% 1.60/1.15  Parsing              : 0.14
% 1.60/1.15  CNF conversion       : 0.01
% 1.60/1.15  Main loop            : 0.10
% 1.60/1.15  Inferencing          : 0.04
% 1.60/1.15  Reduction            : 0.04
% 1.60/1.15  Demodulation         : 0.03
% 1.60/1.15  BG Simplification    : 0.01
% 1.60/1.15  Subsumption          : 0.01
% 1.60/1.15  Abstraction          : 0.01
% 1.60/1.15  MUC search           : 0.00
% 1.60/1.15  Cooper               : 0.00
% 1.60/1.15  Total                : 0.39
% 1.60/1.15  Index Insertion      : 0.00
% 1.60/1.15  Index Deletion       : 0.00
% 1.60/1.15  Index Matching       : 0.00
% 1.60/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
