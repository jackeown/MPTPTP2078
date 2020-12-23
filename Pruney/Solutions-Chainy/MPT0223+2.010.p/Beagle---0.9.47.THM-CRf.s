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
% DateTime   : Thu Dec  3 09:48:18 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_108,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,A_24) = k2_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(B_26,A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_92,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_83])).

tff(c_153,plain,(
    ! [B_31,A_32] : r1_tarski(k3_xboole_0(B_31,A_32),A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_92])).

tff(c_162,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_153])).

tff(c_214,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(k1_tarski(A_38),k1_tarski(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_217,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_162,c_214])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:31:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.20  
% 1.80/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.21  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.80/1.21  
% 1.80/1.21  %Foreground sorts:
% 1.80/1.21  
% 1.80/1.21  
% 1.80/1.21  %Background operators:
% 1.80/1.21  
% 1.80/1.21  
% 1.80/1.21  %Foreground operators:
% 1.80/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.80/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.80/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.80/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.80/1.21  
% 1.80/1.21  tff(f_48, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.80/1.21  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.80/1.21  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.80/1.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.80/1.21  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.80/1.21  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.80/1.21  tff(c_18, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.80/1.21  tff(c_20, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.80/1.21  tff(c_108, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.21  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.21  tff(c_44, plain, (![B_23, A_24]: (k2_xboole_0(B_23, A_24)=k2_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.80/1.21  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.80/1.21  tff(c_83, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(B_26, A_25)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_8])).
% 1.80/1.21  tff(c_92, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_83])).
% 1.80/1.21  tff(c_153, plain, (![B_31, A_32]: (r1_tarski(k3_xboole_0(B_31, A_32), A_32))), inference(superposition, [status(thm), theory('equality')], [c_108, c_92])).
% 1.80/1.21  tff(c_162, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_153])).
% 1.80/1.21  tff(c_214, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(k1_tarski(A_38), k1_tarski(B_37)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.80/1.21  tff(c_217, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_162, c_214])).
% 1.80/1.21  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_217])).
% 1.80/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.21  
% 1.80/1.21  Inference rules
% 1.80/1.21  ----------------------
% 1.80/1.21  #Ref     : 0
% 1.80/1.21  #Sup     : 50
% 1.80/1.21  #Fact    : 0
% 1.80/1.21  #Define  : 0
% 1.80/1.21  #Split   : 0
% 1.80/1.21  #Chain   : 0
% 1.80/1.21  #Close   : 0
% 1.80/1.21  
% 1.80/1.21  Ordering : KBO
% 1.80/1.21  
% 1.80/1.21  Simplification rules
% 1.80/1.21  ----------------------
% 1.80/1.21  #Subsume      : 0
% 1.80/1.21  #Demod        : 12
% 1.80/1.21  #Tautology    : 40
% 1.80/1.21  #SimpNegUnit  : 1
% 1.80/1.21  #BackRed      : 0
% 1.80/1.21  
% 1.80/1.21  #Partial instantiations: 0
% 1.80/1.21  #Strategies tried      : 1
% 1.80/1.21  
% 1.80/1.22  Timing (in seconds)
% 1.80/1.22  ----------------------
% 1.80/1.22  Preprocessing        : 0.26
% 1.80/1.22  Parsing              : 0.14
% 1.80/1.22  CNF conversion       : 0.01
% 1.80/1.22  Main loop            : 0.13
% 1.80/1.22  Inferencing          : 0.05
% 1.80/1.22  Reduction            : 0.05
% 1.80/1.22  Demodulation         : 0.04
% 1.80/1.22  BG Simplification    : 0.01
% 1.80/1.22  Subsumption          : 0.02
% 1.80/1.22  Abstraction          : 0.01
% 1.80/1.22  MUC search           : 0.00
% 1.80/1.22  Cooper               : 0.00
% 1.80/1.22  Total                : 0.41
% 1.80/1.22  Index Insertion      : 0.00
% 1.80/1.22  Index Deletion       : 0.00
% 1.80/1.22  Index Matching       : 0.00
% 1.80/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
