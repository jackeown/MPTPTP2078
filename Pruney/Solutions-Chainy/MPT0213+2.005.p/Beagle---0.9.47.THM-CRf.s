%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:27 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  31 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_26,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_162,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_3'(A_53,B_54),A_53)
      | r2_hidden('#skF_4'(A_53,B_54),B_54)
      | k3_tarski(A_53) = B_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_228,plain,(
    ! [A_57,B_58] :
      ( ~ v1_xboole_0(A_57)
      | r2_hidden('#skF_4'(A_57,B_58),B_58)
      | k3_tarski(A_57) = B_58 ) ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_261,plain,(
    ! [B_59,A_60] :
      ( ~ v1_xboole_0(B_59)
      | ~ v1_xboole_0(A_60)
      | k3_tarski(A_60) = B_59 ) ),
    inference(resolution,[status(thm)],[c_228,c_2])).

tff(c_277,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0(A_61)
      | k3_tarski(A_61) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_261])).

tff(c_292,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_277])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.19  %$ r2_hidden > v1_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.00/1.19  
% 2.00/1.19  %Foreground sorts:
% 2.00/1.19  
% 2.00/1.19  
% 2.00/1.19  %Background operators:
% 2.00/1.19  
% 2.00/1.19  
% 2.00/1.19  %Foreground operators:
% 2.00/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.00/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.00/1.19  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.00/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.00/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.00/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.00/1.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.00/1.19  
% 2.00/1.20  tff(f_44, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.00/1.20  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.00/1.20  tff(f_42, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.00/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.00/1.20  tff(c_26, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.00/1.20  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.00/1.20  tff(c_162, plain, (![A_53, B_54]: (r2_hidden('#skF_3'(A_53, B_54), A_53) | r2_hidden('#skF_4'(A_53, B_54), B_54) | k3_tarski(A_53)=B_54)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.00/1.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.20  tff(c_228, plain, (![A_57, B_58]: (~v1_xboole_0(A_57) | r2_hidden('#skF_4'(A_57, B_58), B_58) | k3_tarski(A_57)=B_58)), inference(resolution, [status(thm)], [c_162, c_2])).
% 2.00/1.20  tff(c_261, plain, (![B_59, A_60]: (~v1_xboole_0(B_59) | ~v1_xboole_0(A_60) | k3_tarski(A_60)=B_59)), inference(resolution, [status(thm)], [c_228, c_2])).
% 2.00/1.20  tff(c_277, plain, (![A_61]: (~v1_xboole_0(A_61) | k3_tarski(A_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_261])).
% 2.00/1.20  tff(c_292, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_277])).
% 2.00/1.20  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_292])).
% 2.00/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.20  
% 2.00/1.20  Inference rules
% 2.00/1.20  ----------------------
% 2.00/1.20  #Ref     : 0
% 2.00/1.20  #Sup     : 58
% 2.00/1.20  #Fact    : 0
% 2.00/1.20  #Define  : 0
% 2.00/1.20  #Split   : 0
% 2.00/1.20  #Chain   : 0
% 2.00/1.20  #Close   : 0
% 2.00/1.20  
% 2.00/1.20  Ordering : KBO
% 2.00/1.20  
% 2.00/1.20  Simplification rules
% 2.00/1.20  ----------------------
% 2.00/1.20  #Subsume      : 6
% 2.00/1.20  #Demod        : 0
% 2.00/1.20  #Tautology    : 3
% 2.00/1.20  #SimpNegUnit  : 1
% 2.00/1.20  #BackRed      : 0
% 2.00/1.20  
% 2.00/1.20  #Partial instantiations: 0
% 2.00/1.20  #Strategies tried      : 1
% 2.00/1.20  
% 2.00/1.20  Timing (in seconds)
% 2.00/1.20  ----------------------
% 2.00/1.20  Preprocessing        : 0.24
% 2.00/1.20  Parsing              : 0.12
% 2.00/1.20  CNF conversion       : 0.02
% 2.00/1.20  Main loop            : 0.19
% 2.00/1.20  Inferencing          : 0.08
% 2.00/1.20  Reduction            : 0.04
% 2.00/1.20  Demodulation         : 0.02
% 2.00/1.20  BG Simplification    : 0.01
% 2.00/1.20  Subsumption          : 0.05
% 2.00/1.20  Abstraction          : 0.01
% 2.00/1.20  MUC search           : 0.00
% 2.00/1.20  Cooper               : 0.00
% 2.00/1.20  Total                : 0.46
% 2.00/1.20  Index Insertion      : 0.00
% 2.00/1.20  Index Deletion       : 0.00
% 2.00/1.20  Index Matching       : 0.00
% 2.00/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
