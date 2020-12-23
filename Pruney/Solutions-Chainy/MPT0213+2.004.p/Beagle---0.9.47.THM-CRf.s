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
% DateTime   : Thu Dec  3 09:47:27 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 123 expanded)
%              Number of leaves         :   32 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :   40 ( 211 expanded)
%              Number of equality atoms :   14 (  55 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3 > #skF_7 > #skF_9 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_114,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_142,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_466,plain,(
    ! [A_239,B_240] :
      ( r2_hidden('#skF_8'(A_239,B_240),A_239)
      | r2_hidden('#skF_9'(A_239,B_240),B_240)
      | k3_tarski(A_239) = B_240 ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_126,plain,(
    ! [A_66,C_81] :
      ( r2_hidden('#skF_10'(A_66,k3_tarski(A_66),C_81),A_66)
      | ~ r2_hidden(C_81,k3_tarski(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_285,plain,(
    ! [A_136,C_137] :
      ( r2_hidden('#skF_10'(A_136,k3_tarski(A_136),C_137),A_136)
      | ~ r2_hidden(C_137,k3_tarski(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_24,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_168,plain,(
    ! [D_97,B_98,A_99] :
      ( ~ r2_hidden(D_97,B_98)
      | ~ r2_hidden(D_97,k4_xboole_0(A_99,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_171,plain,(
    ! [D_97,A_9] :
      ( ~ r2_hidden(D_97,k1_xboole_0)
      | ~ r2_hidden(D_97,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_168])).

tff(c_303,plain,(
    ! [C_138,A_139] :
      ( ~ r2_hidden('#skF_10'(k1_xboole_0,k3_tarski(k1_xboole_0),C_138),A_139)
      | ~ r2_hidden(C_138,k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_285,c_171])).

tff(c_337,plain,(
    ! [C_81] : ~ r2_hidden(C_81,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_126,c_303])).

tff(c_598,plain,(
    ! [B_241] :
      ( r2_hidden('#skF_9'(k3_tarski(k1_xboole_0),B_241),B_241)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_241 ) ),
    inference(resolution,[status(thm)],[c_466,c_337])).

tff(c_662,plain,(
    k3_tarski(k3_tarski(k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_598,c_337])).

tff(c_580,plain,(
    ! [B_240] :
      ( r2_hidden('#skF_9'(k3_tarski(k1_xboole_0),B_240),B_240)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_240 ) ),
    inference(resolution,[status(thm)],[c_466,c_337])).

tff(c_688,plain,(
    ! [B_240] :
      ( r2_hidden('#skF_9'(k3_tarski(k1_xboole_0),B_240),B_240)
      | k3_tarski(k1_xboole_0) = B_240 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_580])).

tff(c_712,plain,(
    ! [B_244] :
      ( r2_hidden('#skF_9'(k3_tarski(k1_xboole_0),B_244),B_244)
      | k3_tarski(k1_xboole_0) = B_244 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_580])).

tff(c_729,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_9'(k3_tarski(k1_xboole_0),k1_xboole_0),A_9)
      | k3_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_712,c_171])).

tff(c_743,plain,(
    ! [A_245] : ~ r2_hidden('#skF_9'(k3_tarski(k1_xboole_0),k1_xboole_0),A_245) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_729])).

tff(c_747,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_688,c_743])).

tff(c_809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_747])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:44:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.61  
% 3.69/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.61  %$ r2_hidden > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3 > #skF_7 > #skF_9 > #skF_10
% 3.69/1.61  
% 3.69/1.61  %Foreground sorts:
% 3.69/1.61  
% 3.69/1.61  
% 3.69/1.61  %Background operators:
% 3.69/1.61  
% 3.69/1.61  
% 3.69/1.61  %Foreground operators:
% 3.69/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.69/1.61  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.69/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.69/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.69/1.61  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.69/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.69/1.61  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.69/1.61  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.69/1.61  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.69/1.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.69/1.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.61  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.69/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.69/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.69/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.69/1.61  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.69/1.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.61  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.69/1.61  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 3.69/1.61  
% 3.69/1.62  tff(f_114, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 3.69/1.62  tff(f_112, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 3.69/1.62  tff(f_40, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.69/1.62  tff(f_36, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.69/1.62  tff(c_142, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.62  tff(c_466, plain, (![A_239, B_240]: (r2_hidden('#skF_8'(A_239, B_240), A_239) | r2_hidden('#skF_9'(A_239, B_240), B_240) | k3_tarski(A_239)=B_240)), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.69/1.62  tff(c_126, plain, (![A_66, C_81]: (r2_hidden('#skF_10'(A_66, k3_tarski(A_66), C_81), A_66) | ~r2_hidden(C_81, k3_tarski(A_66)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.69/1.62  tff(c_285, plain, (![A_136, C_137]: (r2_hidden('#skF_10'(A_136, k3_tarski(A_136), C_137), A_136) | ~r2_hidden(C_137, k3_tarski(A_136)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.69/1.62  tff(c_24, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.69/1.62  tff(c_168, plain, (![D_97, B_98, A_99]: (~r2_hidden(D_97, B_98) | ~r2_hidden(D_97, k4_xboole_0(A_99, B_98)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.69/1.62  tff(c_171, plain, (![D_97, A_9]: (~r2_hidden(D_97, k1_xboole_0) | ~r2_hidden(D_97, A_9))), inference(superposition, [status(thm), theory('equality')], [c_24, c_168])).
% 3.69/1.62  tff(c_303, plain, (![C_138, A_139]: (~r2_hidden('#skF_10'(k1_xboole_0, k3_tarski(k1_xboole_0), C_138), A_139) | ~r2_hidden(C_138, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_285, c_171])).
% 3.69/1.62  tff(c_337, plain, (![C_81]: (~r2_hidden(C_81, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_126, c_303])).
% 3.69/1.62  tff(c_598, plain, (![B_241]: (r2_hidden('#skF_9'(k3_tarski(k1_xboole_0), B_241), B_241) | k3_tarski(k3_tarski(k1_xboole_0))=B_241)), inference(resolution, [status(thm)], [c_466, c_337])).
% 3.69/1.62  tff(c_662, plain, (k3_tarski(k3_tarski(k1_xboole_0))=k3_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_598, c_337])).
% 3.69/1.62  tff(c_580, plain, (![B_240]: (r2_hidden('#skF_9'(k3_tarski(k1_xboole_0), B_240), B_240) | k3_tarski(k3_tarski(k1_xboole_0))=B_240)), inference(resolution, [status(thm)], [c_466, c_337])).
% 3.69/1.62  tff(c_688, plain, (![B_240]: (r2_hidden('#skF_9'(k3_tarski(k1_xboole_0), B_240), B_240) | k3_tarski(k1_xboole_0)=B_240)), inference(demodulation, [status(thm), theory('equality')], [c_662, c_580])).
% 3.69/1.62  tff(c_712, plain, (![B_244]: (r2_hidden('#skF_9'(k3_tarski(k1_xboole_0), B_244), B_244) | k3_tarski(k1_xboole_0)=B_244)), inference(demodulation, [status(thm), theory('equality')], [c_662, c_580])).
% 3.69/1.62  tff(c_729, plain, (![A_9]: (~r2_hidden('#skF_9'(k3_tarski(k1_xboole_0), k1_xboole_0), A_9) | k3_tarski(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_712, c_171])).
% 3.69/1.62  tff(c_743, plain, (![A_245]: (~r2_hidden('#skF_9'(k3_tarski(k1_xboole_0), k1_xboole_0), A_245))), inference(negUnitSimplification, [status(thm)], [c_142, c_729])).
% 3.69/1.62  tff(c_747, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_688, c_743])).
% 3.69/1.62  tff(c_809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_747])).
% 3.69/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.62  
% 3.69/1.62  Inference rules
% 3.69/1.62  ----------------------
% 3.69/1.62  #Ref     : 0
% 3.69/1.62  #Sup     : 144
% 3.69/1.62  #Fact    : 0
% 3.69/1.62  #Define  : 0
% 3.69/1.62  #Split   : 0
% 3.69/1.62  #Chain   : 0
% 3.69/1.62  #Close   : 0
% 3.69/1.62  
% 3.69/1.62  Ordering : KBO
% 3.69/1.62  
% 3.69/1.62  Simplification rules
% 3.69/1.62  ----------------------
% 3.69/1.62  #Subsume      : 19
% 3.69/1.62  #Demod        : 45
% 3.69/1.62  #Tautology    : 34
% 3.69/1.62  #SimpNegUnit  : 3
% 3.69/1.62  #BackRed      : 9
% 3.69/1.62  
% 3.69/1.62  #Partial instantiations: 0
% 3.69/1.62  #Strategies tried      : 1
% 3.69/1.62  
% 3.69/1.62  Timing (in seconds)
% 3.69/1.62  ----------------------
% 3.69/1.63  Preprocessing        : 0.41
% 3.69/1.63  Parsing              : 0.18
% 3.69/1.63  CNF conversion       : 0.03
% 3.69/1.63  Main loop            : 0.47
% 3.69/1.63  Inferencing          : 0.12
% 3.69/1.63  Reduction            : 0.15
% 3.69/1.63  Demodulation         : 0.11
% 3.69/1.63  BG Simplification    : 0.03
% 3.69/1.63  Subsumption          : 0.15
% 3.69/1.63  Abstraction          : 0.04
% 3.69/1.63  MUC search           : 0.00
% 3.69/1.63  Cooper               : 0.00
% 3.69/1.63  Total                : 0.90
% 3.69/1.63  Index Insertion      : 0.00
% 3.69/1.63  Index Deletion       : 0.00
% 3.69/1.63  Index Matching       : 0.00
% 3.69/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
