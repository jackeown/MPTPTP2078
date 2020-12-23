%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:29 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_32,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_102,plain,(
    ! [A_47,C_48] :
      ( r2_hidden('#skF_6'(A_47,k3_tarski(A_47),C_48),A_47)
      | ~ r2_hidden(C_48,k3_tarski(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,B_35)
      | ~ r2_hidden(C_36,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    ! [C_36] : ~ r2_hidden(C_36,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_42])).

tff(c_111,plain,(
    ! [C_49] : ~ r2_hidden(C_49,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_102,c_45])).

tff(c_131,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_111])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:47:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.12  %$ r2_hidden > r1_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
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
% 1.65/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.65/1.12  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.65/1.12  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.65/1.12  
% 1.75/1.12  tff(f_75, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.75/1.12  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.75/1.12  tff(f_73, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 1.75/1.12  tff(f_63, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.75/1.12  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.75/1.12  tff(c_32, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.75/1.12  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.75/1.12  tff(c_102, plain, (![A_47, C_48]: (r2_hidden('#skF_6'(A_47, k3_tarski(A_47), C_48), A_47) | ~r2_hidden(C_48, k3_tarski(A_47)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.75/1.12  tff(c_10, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.75/1.12  tff(c_42, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, B_35) | ~r2_hidden(C_36, A_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.75/1.12  tff(c_45, plain, (![C_36]: (~r2_hidden(C_36, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_42])).
% 1.75/1.12  tff(c_111, plain, (![C_49]: (~r2_hidden(C_49, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_102, c_45])).
% 1.75/1.12  tff(c_131, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_111])).
% 1.75/1.12  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_131])).
% 1.75/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.12  
% 1.75/1.12  Inference rules
% 1.75/1.12  ----------------------
% 1.75/1.12  #Ref     : 0
% 1.75/1.12  #Sup     : 21
% 1.75/1.12  #Fact    : 0
% 1.75/1.12  #Define  : 0
% 1.75/1.12  #Split   : 0
% 1.75/1.12  #Chain   : 0
% 1.75/1.12  #Close   : 0
% 1.75/1.12  
% 1.75/1.12  Ordering : KBO
% 1.75/1.12  
% 1.75/1.12  Simplification rules
% 1.75/1.12  ----------------------
% 1.75/1.12  #Subsume      : 2
% 1.75/1.12  #Demod        : 1
% 1.75/1.12  #Tautology    : 6
% 1.75/1.12  #SimpNegUnit  : 1
% 1.75/1.12  #BackRed      : 0
% 1.75/1.12  
% 1.75/1.12  #Partial instantiations: 0
% 1.75/1.12  #Strategies tried      : 1
% 1.75/1.12  
% 1.75/1.12  Timing (in seconds)
% 1.75/1.12  ----------------------
% 1.75/1.13  Preprocessing        : 0.27
% 1.75/1.13  Parsing              : 0.14
% 1.75/1.13  CNF conversion       : 0.02
% 1.75/1.13  Main loop            : 0.12
% 1.75/1.13  Inferencing          : 0.05
% 1.75/1.13  Reduction            : 0.03
% 1.75/1.13  Demodulation         : 0.02
% 1.75/1.13  BG Simplification    : 0.01
% 1.75/1.13  Subsumption          : 0.03
% 1.75/1.13  Abstraction          : 0.01
% 1.75/1.13  MUC search           : 0.00
% 1.75/1.13  Cooper               : 0.00
% 1.75/1.13  Total                : 0.41
% 1.75/1.13  Index Insertion      : 0.00
% 1.75/1.13  Index Deletion       : 0.00
% 1.75/1.13  Index Matching       : 0.00
% 1.75/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
