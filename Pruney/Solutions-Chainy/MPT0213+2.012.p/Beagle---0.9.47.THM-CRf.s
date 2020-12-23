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
% DateTime   : Thu Dec  3 09:47:28 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_28,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_140,plain,(
    ! [A_53,C_54] :
      ( r2_hidden('#skF_6'(A_53,k3_tarski(A_53),C_54),A_53)
      | ~ r2_hidden(C_54,k3_tarski(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_xboole_0(k3_xboole_0(A_8,B_9),k5_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r1_xboole_0(A_32,B_33)
      | ~ r2_hidden(C_34,k3_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,(
    ! [A_35,B_36] :
      ( ~ r1_xboole_0(A_35,B_36)
      | k3_xboole_0(A_35,B_36) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_31])).

tff(c_46,plain,(
    ! [A_40,B_41] : k3_xboole_0(k3_xboole_0(A_40,B_41),k5_xboole_0(A_40,B_41)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_37])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    ! [A_40,B_41,C_5] :
      ( ~ r1_xboole_0(k3_xboole_0(A_40,B_41),k5_xboole_0(A_40,B_41))
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4])).

tff(c_65,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_54])).

tff(c_154,plain,(
    ! [C_55] : ~ r2_hidden(C_55,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_140,c_65])).

tff(c_166,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_154])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:51:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.59  
% 2.20/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.60  %$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.20/1.60  
% 2.20/1.60  %Foreground sorts:
% 2.20/1.60  
% 2.20/1.60  
% 2.20/1.60  %Background operators:
% 2.20/1.60  
% 2.20/1.60  
% 2.20/1.60  %Foreground operators:
% 2.20/1.60  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.20/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.60  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.20/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.20/1.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.20/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.20/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.20/1.60  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.20/1.60  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.20/1.60  
% 2.20/1.61  tff(f_61, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.20/1.61  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.20/1.61  tff(f_59, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.20/1.61  tff(f_49, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 2.20/1.61  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.20/1.61  tff(c_28, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.20/1.61  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.20/1.61  tff(c_140, plain, (![A_53, C_54]: (r2_hidden('#skF_6'(A_53, k3_tarski(A_53), C_54), A_53) | ~r2_hidden(C_54, k3_tarski(A_53)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.20/1.61  tff(c_8, plain, (![A_8, B_9]: (r1_xboole_0(k3_xboole_0(A_8, B_9), k5_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.20/1.61  tff(c_31, plain, (![A_32, B_33, C_34]: (~r1_xboole_0(A_32, B_33) | ~r2_hidden(C_34, k3_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.61  tff(c_37, plain, (![A_35, B_36]: (~r1_xboole_0(A_35, B_36) | k3_xboole_0(A_35, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_31])).
% 2.20/1.61  tff(c_46, plain, (![A_40, B_41]: (k3_xboole_0(k3_xboole_0(A_40, B_41), k5_xboole_0(A_40, B_41))=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_37])).
% 2.20/1.61  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.61  tff(c_54, plain, (![A_40, B_41, C_5]: (~r1_xboole_0(k3_xboole_0(A_40, B_41), k5_xboole_0(A_40, B_41)) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_4])).
% 2.20/1.61  tff(c_65, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_54])).
% 2.20/1.61  tff(c_154, plain, (![C_55]: (~r2_hidden(C_55, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_140, c_65])).
% 2.20/1.61  tff(c_166, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_154])).
% 2.20/1.61  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_166])).
% 2.20/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.61  
% 2.20/1.61  Inference rules
% 2.20/1.61  ----------------------
% 2.20/1.61  #Ref     : 0
% 2.20/1.61  #Sup     : 33
% 2.20/1.61  #Fact    : 0
% 2.20/1.61  #Define  : 0
% 2.20/1.61  #Split   : 0
% 2.20/1.61  #Chain   : 0
% 2.20/1.61  #Close   : 0
% 2.20/1.61  
% 2.20/1.61  Ordering : KBO
% 2.20/1.61  
% 2.20/1.61  Simplification rules
% 2.20/1.61  ----------------------
% 2.20/1.61  #Subsume      : 1
% 2.20/1.61  #Demod        : 6
% 2.20/1.61  #Tautology    : 11
% 2.20/1.61  #SimpNegUnit  : 3
% 2.20/1.61  #BackRed      : 0
% 2.20/1.61  
% 2.20/1.61  #Partial instantiations: 0
% 2.20/1.61  #Strategies tried      : 1
% 2.20/1.61  
% 2.20/1.61  Timing (in seconds)
% 2.20/1.61  ----------------------
% 2.20/1.61  Preprocessing        : 0.43
% 2.20/1.61  Parsing              : 0.22
% 2.20/1.62  CNF conversion       : 0.04
% 2.20/1.62  Main loop            : 0.23
% 2.20/1.62  Inferencing          : 0.09
% 2.20/1.62  Reduction            : 0.06
% 2.20/1.62  Demodulation         : 0.05
% 2.20/1.62  BG Simplification    : 0.02
% 2.20/1.62  Subsumption          : 0.04
% 2.20/1.62  Abstraction          : 0.01
% 2.20/1.62  MUC search           : 0.00
% 2.20/1.62  Cooper               : 0.00
% 2.20/1.62  Total                : 0.70
% 2.20/1.62  Index Insertion      : 0.00
% 2.20/1.62  Index Deletion       : 0.00
% 2.20/1.62  Index Matching       : 0.00
% 2.20/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
