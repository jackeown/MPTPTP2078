%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:24 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_2'(A_15,B_16),B_16)
      | r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [B_19,A_20] :
      ( ~ v1_xboole_0(B_19)
      | r1_xboole_0(A_20,B_19) ) ),
    inference(resolution,[status(thm)],[c_26,c_2])).

tff(c_14,plain,(
    ~ r1_xboole_0('#skF_3',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_39,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_14])).

tff(c_43,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:31:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.41  
% 1.91/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.41  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.91/1.41  
% 1.91/1.41  %Foreground sorts:
% 1.91/1.41  
% 1.91/1.41  
% 1.91/1.41  %Background operators:
% 1.91/1.41  
% 1.91/1.41  
% 1.91/1.41  %Foreground operators:
% 1.91/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.91/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.41  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.41  
% 1.91/1.42  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.91/1.42  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.91/1.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.91/1.42  tff(f_53, negated_conjecture, ~(![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.91/1.42  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.42  tff(c_26, plain, (![A_15, B_16]: (r2_hidden('#skF_2'(A_15, B_16), B_16) | r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.42  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.42  tff(c_36, plain, (![B_19, A_20]: (~v1_xboole_0(B_19) | r1_xboole_0(A_20, B_19))), inference(resolution, [status(thm)], [c_26, c_2])).
% 1.91/1.42  tff(c_14, plain, (~r1_xboole_0('#skF_3', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.42  tff(c_39, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_14])).
% 1.91/1.42  tff(c_43, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_39])).
% 1.91/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.42  
% 1.91/1.42  Inference rules
% 1.91/1.42  ----------------------
% 1.91/1.42  #Ref     : 0
% 1.91/1.42  #Sup     : 5
% 1.91/1.42  #Fact    : 0
% 1.91/1.42  #Define  : 0
% 1.91/1.42  #Split   : 0
% 1.91/1.42  #Chain   : 0
% 1.91/1.42  #Close   : 0
% 1.91/1.42  
% 1.91/1.42  Ordering : KBO
% 1.91/1.42  
% 1.91/1.42  Simplification rules
% 1.91/1.42  ----------------------
% 1.91/1.42  #Subsume      : 0
% 1.91/1.42  #Demod        : 1
% 1.91/1.42  #Tautology    : 1
% 1.91/1.42  #SimpNegUnit  : 0
% 1.91/1.42  #BackRed      : 0
% 1.91/1.42  
% 1.91/1.42  #Partial instantiations: 0
% 1.91/1.42  #Strategies tried      : 1
% 1.91/1.42  
% 1.91/1.42  Timing (in seconds)
% 1.91/1.42  ----------------------
% 1.91/1.43  Preprocessing        : 0.38
% 1.91/1.43  Parsing              : 0.21
% 1.91/1.43  CNF conversion       : 0.03
% 1.91/1.43  Main loop            : 0.15
% 1.91/1.43  Inferencing          : 0.08
% 1.91/1.43  Reduction            : 0.03
% 1.91/1.43  Demodulation         : 0.02
% 1.91/1.43  BG Simplification    : 0.02
% 1.91/1.43  Subsumption          : 0.02
% 1.91/1.43  Abstraction          : 0.01
% 1.91/1.43  MUC search           : 0.00
% 1.91/1.43  Cooper               : 0.00
% 1.91/1.43  Total                : 0.57
% 1.91/1.43  Index Insertion      : 0.00
% 1.91/1.43  Index Deletion       : 0.00
% 1.91/1.43  Index Matching       : 0.00
% 1.91/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
