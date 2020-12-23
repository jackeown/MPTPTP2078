%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:25 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 102 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   39 ( 105 expanded)
%              Number of equality atoms :   25 (  91 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_98,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,(
    ! [A_25,B_26] :
      ( k1_xboole_0 = A_25
      | k2_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_58])).

tff(c_72,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_34])).

tff(c_113,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_72])).

tff(c_159,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_113])).

tff(c_236,plain,(
    ! [A_35] : k2_xboole_0(A_35,'#skF_4') = A_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_6])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_180,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_8])).

tff(c_246,plain,(
    ! [A_35] : k4_xboole_0(A_35,A_35) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_180])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_16])).

tff(c_169,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_79])).

tff(c_170,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_65])).

tff(c_457,plain,(
    ! [A_51,B_52] :
      ( ~ r2_hidden(A_51,B_52)
      | ~ r1_xboole_0(k1_tarski(A_51),B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_490,plain,(
    ! [B_54] :
      ( ~ r2_hidden('#skF_3',B_54)
      | ~ r1_xboole_0('#skF_4',B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_457])).

tff(c_498,plain,(
    ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_169,c_490])).

tff(c_503,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_498])).

tff(c_507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:57:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  
% 2.12/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.29  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.12/1.29  
% 2.12/1.29  %Foreground sorts:
% 2.12/1.29  
% 2.12/1.29  
% 2.12/1.29  %Background operators:
% 2.12/1.29  
% 2.12/1.29  
% 2.12/1.29  %Foreground operators:
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.12/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.29  
% 2.12/1.30  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.12/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.12/1.30  tff(f_61, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.12/1.30  tff(f_31, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.12/1.30  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.12/1.30  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.12/1.30  tff(f_46, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.12/1.30  tff(f_55, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.12/1.30  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.30  tff(c_98, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.30  tff(c_34, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.30  tff(c_58, plain, (![A_25, B_26]: (k1_xboole_0=A_25 | k2_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.30  tff(c_65, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34, c_58])).
% 2.12/1.30  tff(c_72, plain, (k2_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_65, c_34])).
% 2.12/1.30  tff(c_113, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_98, c_72])).
% 2.12/1.30  tff(c_159, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_113])).
% 2.12/1.30  tff(c_236, plain, (![A_35]: (k2_xboole_0(A_35, '#skF_4')=A_35)), inference(demodulation, [status(thm), theory('equality')], [c_159, c_6])).
% 2.12/1.30  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(A_6, B_7))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.30  tff(c_180, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(A_6, B_7))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_8])).
% 2.12/1.30  tff(c_246, plain, (![A_35]: (k4_xboole_0(A_35, A_35)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_236, c_180])).
% 2.12/1.30  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.30  tff(c_16, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.30  tff(c_79, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_65, c_16])).
% 2.12/1.30  tff(c_169, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_79])).
% 2.12/1.30  tff(c_170, plain, (k1_tarski('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_65])).
% 2.12/1.30  tff(c_457, plain, (![A_51, B_52]: (~r2_hidden(A_51, B_52) | ~r1_xboole_0(k1_tarski(A_51), B_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.12/1.30  tff(c_490, plain, (![B_54]: (~r2_hidden('#skF_3', B_54) | ~r1_xboole_0('#skF_4', B_54))), inference(superposition, [status(thm), theory('equality')], [c_170, c_457])).
% 2.12/1.30  tff(c_498, plain, (~r1_xboole_0('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_169, c_490])).
% 2.12/1.30  tff(c_503, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_12, c_498])).
% 2.12/1.30  tff(c_507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_246, c_503])).
% 2.12/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  Inference rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Ref     : 0
% 2.12/1.30  #Sup     : 121
% 2.12/1.30  #Fact    : 0
% 2.12/1.30  #Define  : 0
% 2.12/1.30  #Split   : 1
% 2.12/1.30  #Chain   : 0
% 2.12/1.30  #Close   : 0
% 2.12/1.30  
% 2.12/1.30  Ordering : KBO
% 2.12/1.30  
% 2.12/1.30  Simplification rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Subsume      : 11
% 2.12/1.30  #Demod        : 48
% 2.12/1.30  #Tautology    : 89
% 2.12/1.30  #SimpNegUnit  : 0
% 2.12/1.30  #BackRed      : 7
% 2.12/1.30  
% 2.12/1.30  #Partial instantiations: 0
% 2.12/1.30  #Strategies tried      : 1
% 2.12/1.30  
% 2.12/1.30  Timing (in seconds)
% 2.12/1.30  ----------------------
% 2.12/1.30  Preprocessing        : 0.30
% 2.12/1.30  Parsing              : 0.16
% 2.12/1.30  CNF conversion       : 0.02
% 2.12/1.30  Main loop            : 0.22
% 2.12/1.30  Inferencing          : 0.07
% 2.12/1.30  Reduction            : 0.08
% 2.12/1.30  Demodulation         : 0.06
% 2.12/1.30  BG Simplification    : 0.01
% 2.12/1.30  Subsumption          : 0.04
% 2.12/1.30  Abstraction          : 0.01
% 2.12/1.30  MUC search           : 0.00
% 2.12/1.30  Cooper               : 0.00
% 2.12/1.30  Total                : 0.55
% 2.12/1.30  Index Insertion      : 0.00
% 2.12/1.30  Index Deletion       : 0.00
% 2.12/1.30  Index Matching       : 0.00
% 2.12/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
