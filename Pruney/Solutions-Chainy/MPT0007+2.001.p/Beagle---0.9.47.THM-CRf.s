%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:28 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_44,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_10,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_12] :
      ( v1_xboole_0(A_12)
      | r2_hidden('#skF_1'(A_12),A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_7] : ~ r2_hidden(B_7,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_23,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_8])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_23,c_6])).

tff(c_30,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:29:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.13  
% 1.56/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.14  %$ r2_hidden > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2
% 1.56/1.14  
% 1.56/1.14  %Foreground sorts:
% 1.56/1.14  
% 1.56/1.14  
% 1.56/1.14  %Background operators:
% 1.56/1.14  
% 1.56/1.14  
% 1.56/1.14  %Foreground operators:
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.56/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.56/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.56/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.56/1.14  
% 1.56/1.14  tff(f_44, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.56/1.14  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.56/1.14  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.56/1.14  tff(c_10, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.56/1.14  tff(c_14, plain, (![A_12]: (v1_xboole_0(A_12) | r2_hidden('#skF_1'(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.56/1.14  tff(c_8, plain, (![B_7]: (~r2_hidden(B_7, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.56/1.14  tff(c_23, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_8])).
% 1.56/1.14  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.56/1.14  tff(c_26, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_23, c_6])).
% 1.56/1.14  tff(c_30, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_26])).
% 1.56/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.14  
% 1.56/1.14  Inference rules
% 1.56/1.14  ----------------------
% 1.56/1.14  #Ref     : 0
% 1.56/1.14  #Sup     : 3
% 1.56/1.14  #Fact    : 0
% 1.56/1.14  #Define  : 0
% 1.56/1.14  #Split   : 0
% 1.56/1.14  #Chain   : 0
% 1.56/1.14  #Close   : 0
% 1.56/1.14  
% 1.56/1.14  Ordering : KBO
% 1.56/1.14  
% 1.56/1.14  Simplification rules
% 1.56/1.14  ----------------------
% 1.56/1.14  #Subsume      : 0
% 1.56/1.14  #Demod        : 0
% 1.56/1.14  #Tautology    : 1
% 1.56/1.14  #SimpNegUnit  : 1
% 1.56/1.14  #BackRed      : 0
% 1.56/1.14  
% 1.56/1.14  #Partial instantiations: 0
% 1.56/1.14  #Strategies tried      : 1
% 1.56/1.14  
% 1.56/1.14  Timing (in seconds)
% 1.56/1.14  ----------------------
% 1.56/1.14  Preprocessing        : 0.26
% 1.56/1.14  Parsing              : 0.14
% 1.56/1.14  CNF conversion       : 0.02
% 1.56/1.15  Main loop            : 0.06
% 1.56/1.15  Inferencing          : 0.03
% 1.56/1.15  Reduction            : 0.01
% 1.56/1.15  Demodulation         : 0.00
% 1.56/1.15  BG Simplification    : 0.01
% 1.56/1.15  Subsumption          : 0.00
% 1.56/1.15  Abstraction          : 0.00
% 1.56/1.15  MUC search           : 0.00
% 1.56/1.15  Cooper               : 0.00
% 1.56/1.15  Total                : 0.34
% 1.56/1.15  Index Insertion      : 0.00
% 1.56/1.15  Index Deletion       : 0.00
% 1.56/1.15  Index Matching       : 0.00
% 1.56/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
