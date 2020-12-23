%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:29 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_28,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    ! [A_42,C_43] :
      ( r2_hidden('#skF_6'(A_42,k3_tarski(A_42),C_43),A_42)
      | ~ r2_hidden(C_43,k3_tarski(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ r1_xboole_0(A_30,B_31)
      | ~ r2_hidden(C_32,k3_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,(
    ! [A_33,B_34] :
      ( ~ r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_31])).

tff(c_46,plain,(
    ! [A_38] : k3_xboole_0(A_38,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_37])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_38,C_5] :
      ( ~ r1_xboole_0(A_38,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4])).

tff(c_56,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_51])).

tff(c_92,plain,(
    ! [C_44] : ~ r2_hidden(C_44,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_78,c_56])).

tff(c_100,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 1.65/1.12  
% 1.65/1.12  %Foreground sorts:
% 1.65/1.12  
% 1.65/1.12  
% 1.65/1.12  %Background operators:
% 1.65/1.12  
% 1.65/1.12  
% 1.65/1.12  %Foreground operators:
% 1.65/1.12  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.12  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.65/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.65/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.65/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.65/1.12  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.65/1.12  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.65/1.12  
% 1.65/1.13  tff(f_61, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.65/1.13  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.65/1.13  tff(f_59, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 1.65/1.13  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.65/1.13  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.65/1.13  tff(c_28, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.65/1.13  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.65/1.13  tff(c_78, plain, (![A_42, C_43]: (r2_hidden('#skF_6'(A_42, k3_tarski(A_42), C_43), A_42) | ~r2_hidden(C_43, k3_tarski(A_42)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.65/1.13  tff(c_8, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.65/1.13  tff(c_31, plain, (![A_30, B_31, C_32]: (~r1_xboole_0(A_30, B_31) | ~r2_hidden(C_32, k3_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.65/1.13  tff(c_37, plain, (![A_33, B_34]: (~r1_xboole_0(A_33, B_34) | k3_xboole_0(A_33, B_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_31])).
% 1.65/1.13  tff(c_46, plain, (![A_38]: (k3_xboole_0(A_38, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_37])).
% 1.65/1.13  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.65/1.13  tff(c_51, plain, (![A_38, C_5]: (~r1_xboole_0(A_38, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_4])).
% 1.65/1.13  tff(c_56, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_51])).
% 1.65/1.13  tff(c_92, plain, (![C_44]: (~r2_hidden(C_44, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_78, c_56])).
% 1.65/1.13  tff(c_100, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_92])).
% 1.65/1.13  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_100])).
% 1.65/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  Inference rules
% 1.65/1.13  ----------------------
% 1.65/1.13  #Ref     : 0
% 1.65/1.13  #Sup     : 15
% 1.65/1.13  #Fact    : 0
% 1.65/1.13  #Define  : 0
% 1.65/1.13  #Split   : 0
% 1.65/1.13  #Chain   : 0
% 1.65/1.13  #Close   : 0
% 1.65/1.13  
% 1.65/1.13  Ordering : KBO
% 1.65/1.13  
% 1.65/1.13  Simplification rules
% 1.65/1.13  ----------------------
% 1.65/1.13  #Subsume      : 0
% 1.65/1.13  #Demod        : 2
% 1.65/1.13  #Tautology    : 5
% 1.65/1.13  #SimpNegUnit  : 2
% 1.65/1.13  #BackRed      : 0
% 1.65/1.13  
% 1.65/1.13  #Partial instantiations: 0
% 1.65/1.13  #Strategies tried      : 1
% 1.65/1.13  
% 1.65/1.13  Timing (in seconds)
% 1.65/1.13  ----------------------
% 1.65/1.13  Preprocessing        : 0.27
% 1.65/1.13  Parsing              : 0.15
% 1.65/1.13  CNF conversion       : 0.02
% 1.65/1.13  Main loop            : 0.11
% 1.65/1.13  Inferencing          : 0.05
% 1.65/1.13  Reduction            : 0.03
% 1.65/1.13  Demodulation         : 0.02
% 1.65/1.13  BG Simplification    : 0.01
% 1.65/1.13  Subsumption          : 0.02
% 1.65/1.13  Abstraction          : 0.01
% 1.65/1.13  MUC search           : 0.00
% 1.65/1.13  Cooper               : 0.00
% 1.65/1.13  Total                : 0.40
% 1.65/1.13  Index Insertion      : 0.00
% 1.65/1.13  Index Deletion       : 0.00
% 1.65/1.13  Index Matching       : 0.00
% 1.65/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
