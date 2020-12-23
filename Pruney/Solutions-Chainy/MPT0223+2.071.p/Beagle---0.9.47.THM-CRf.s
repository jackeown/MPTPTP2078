%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:26 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  42 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_32,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(k1_tarski(A_25),B_26)
      | r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    ! [B_28,A_29] :
      ( ~ r2_hidden(B_28,A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [C_14] : ~ v1_xboole_0(k1_tarski(C_14)) ),
    inference(resolution,[status(thm)],[c_12,c_36])).

tff(c_34,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,B_41)
      | ~ r2_hidden(C_42,k3_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [A_43,B_44] :
      ( ~ r1_xboole_0(A_43,B_44)
      | v1_xboole_0(k3_xboole_0(A_43,B_44)) ) ),
    inference(resolution,[status(thm)],[c_4,c_97])).

tff(c_109,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6'))
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_106])).

tff(c_110,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_109])).

tff(c_114,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_110])).

tff(c_10,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_117,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_114,c_10])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:54:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.56  
% 2.07/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.56  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.26/1.56  
% 2.26/1.56  %Foreground sorts:
% 2.26/1.56  
% 2.26/1.56  
% 2.26/1.56  %Background operators:
% 2.26/1.56  
% 2.26/1.56  
% 2.26/1.56  %Foreground operators:
% 2.26/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.26/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.26/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.56  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.56  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.26/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.26/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.26/1.56  
% 2.26/1.58  tff(f_70, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.26/1.58  tff(f_65, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.26/1.58  tff(f_52, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.26/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.26/1.58  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.26/1.58  tff(c_32, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.58  tff(c_30, plain, (![A_25, B_26]: (r1_xboole_0(k1_tarski(A_25), B_26) | r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.58  tff(c_12, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.26/1.58  tff(c_36, plain, (![B_28, A_29]: (~r2_hidden(B_28, A_29) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.58  tff(c_40, plain, (![C_14]: (~v1_xboole_0(k1_tarski(C_14)))), inference(resolution, [status(thm)], [c_12, c_36])).
% 2.26/1.58  tff(c_34, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.58  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.58  tff(c_97, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, B_41) | ~r2_hidden(C_42, k3_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.26/1.58  tff(c_106, plain, (![A_43, B_44]: (~r1_xboole_0(A_43, B_44) | v1_xboole_0(k3_xboole_0(A_43, B_44)))), inference(resolution, [status(thm)], [c_4, c_97])).
% 2.26/1.58  tff(c_109, plain, (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6')) | v1_xboole_0(k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_106])).
% 2.26/1.58  tff(c_110, plain, (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_40, c_109])).
% 2.26/1.58  tff(c_114, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_110])).
% 2.26/1.58  tff(c_10, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.26/1.58  tff(c_117, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_114, c_10])).
% 2.26/1.58  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_117])).
% 2.26/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.58  
% 2.26/1.58  Inference rules
% 2.26/1.58  ----------------------
% 2.26/1.58  #Ref     : 0
% 2.26/1.58  #Sup     : 19
% 2.26/1.58  #Fact    : 0
% 2.26/1.58  #Define  : 0
% 2.26/1.58  #Split   : 0
% 2.26/1.58  #Chain   : 0
% 2.26/1.58  #Close   : 0
% 2.26/1.58  
% 2.26/1.58  Ordering : KBO
% 2.26/1.58  
% 2.26/1.58  Simplification rules
% 2.26/1.58  ----------------------
% 2.26/1.58  #Subsume      : 0
% 2.26/1.58  #Demod        : 1
% 2.26/1.58  #Tautology    : 11
% 2.26/1.58  #SimpNegUnit  : 4
% 2.26/1.58  #BackRed      : 0
% 2.26/1.58  
% 2.26/1.58  #Partial instantiations: 0
% 2.26/1.58  #Strategies tried      : 1
% 2.26/1.58  
% 2.26/1.58  Timing (in seconds)
% 2.26/1.58  ----------------------
% 2.26/1.59  Preprocessing        : 0.47
% 2.26/1.59  Parsing              : 0.24
% 2.26/1.59  CNF conversion       : 0.04
% 2.26/1.59  Main loop            : 0.18
% 2.26/1.59  Inferencing          : 0.07
% 2.26/1.59  Reduction            : 0.06
% 2.26/1.59  Demodulation         : 0.03
% 2.26/1.59  BG Simplification    : 0.02
% 2.26/1.59  Subsumption          : 0.03
% 2.26/1.59  Abstraction          : 0.01
% 2.26/1.59  MUC search           : 0.00
% 2.26/1.59  Cooper               : 0.00
% 2.26/1.59  Total                : 0.69
% 2.26/1.59  Index Insertion      : 0.00
% 2.26/1.59  Index Deletion       : 0.00
% 2.26/1.59  Index Matching       : 0.00
% 2.26/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
