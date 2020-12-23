%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:34 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  43 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_26,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden('#skF_2'(A_30,B_31,C_32),B_31)
      | ~ r2_hidden(A_30,k9_relat_1(C_32,B_31))
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden(A_27,B_28)
      | k4_xboole_0(k1_tarski(A_27),B_28) != k1_tarski(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_91,plain,(
    ! [A_27] : ~ r2_hidden(A_27,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_82])).

tff(c_109,plain,(
    ! [A_33,C_34] :
      ( ~ r2_hidden(A_33,k9_relat_1(C_34,k1_xboole_0))
      | ~ v1_relat_1(C_34) ) ),
    inference(resolution,[status(thm)],[c_99,c_91])).

tff(c_120,plain,(
    ! [C_35] :
      ( ~ v1_relat_1(C_35)
      | v1_xboole_0(k9_relat_1(C_35,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    ! [B_22,A_23] :
      ( ~ v1_xboole_0(B_22)
      | B_22 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,(
    ! [A_23] :
      ( k1_xboole_0 = A_23
      | ~ v1_xboole_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_133,plain,(
    ! [C_39] :
      ( k9_relat_1(C_39,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_39) ) ),
    inference(resolution,[status(thm)],[c_120,c_56])).

tff(c_136,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_133])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.18  
% 1.76/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.18  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.76/1.18  
% 1.76/1.18  %Foreground sorts:
% 1.76/1.18  
% 1.76/1.18  
% 1.76/1.18  %Background operators:
% 1.76/1.18  
% 1.76/1.18  
% 1.76/1.18  %Foreground operators:
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.76/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.76/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.76/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.76/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.76/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.76/1.18  
% 1.85/1.19  tff(f_65, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 1.85/1.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.85/1.19  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 1.85/1.19  tff(f_34, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.85/1.19  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.85/1.19  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.85/1.19  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.85/1.19  tff(c_26, plain, (k9_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.19  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.19  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.19  tff(c_99, plain, (![A_30, B_31, C_32]: (r2_hidden('#skF_2'(A_30, B_31, C_32), B_31) | ~r2_hidden(A_30, k9_relat_1(C_32, B_31)) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.19  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.85/1.19  tff(c_82, plain, (![A_27, B_28]: (~r2_hidden(A_27, B_28) | k4_xboole_0(k1_tarski(A_27), B_28)!=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.85/1.19  tff(c_91, plain, (![A_27]: (~r2_hidden(A_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_82])).
% 1.85/1.19  tff(c_109, plain, (![A_33, C_34]: (~r2_hidden(A_33, k9_relat_1(C_34, k1_xboole_0)) | ~v1_relat_1(C_34))), inference(resolution, [status(thm)], [c_99, c_91])).
% 1.85/1.19  tff(c_120, plain, (![C_35]: (~v1_relat_1(C_35) | v1_xboole_0(k9_relat_1(C_35, k1_xboole_0)))), inference(resolution, [status(thm)], [c_4, c_109])).
% 1.85/1.19  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.19  tff(c_53, plain, (![B_22, A_23]: (~v1_xboole_0(B_22) | B_22=A_23 | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.85/1.19  tff(c_56, plain, (![A_23]: (k1_xboole_0=A_23 | ~v1_xboole_0(A_23))), inference(resolution, [status(thm)], [c_6, c_53])).
% 1.85/1.19  tff(c_133, plain, (![C_39]: (k9_relat_1(C_39, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_39))), inference(resolution, [status(thm)], [c_120, c_56])).
% 1.85/1.19  tff(c_136, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_133])).
% 1.85/1.19  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_136])).
% 1.85/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  Inference rules
% 1.85/1.19  ----------------------
% 1.85/1.19  #Ref     : 0
% 1.85/1.19  #Sup     : 22
% 1.85/1.19  #Fact    : 0
% 1.85/1.19  #Define  : 0
% 1.85/1.19  #Split   : 0
% 1.85/1.19  #Chain   : 0
% 1.85/1.19  #Close   : 0
% 1.85/1.19  
% 1.85/1.19  Ordering : KBO
% 1.85/1.19  
% 1.85/1.19  Simplification rules
% 1.85/1.19  ----------------------
% 1.85/1.19  #Subsume      : 0
% 1.85/1.19  #Demod        : 1
% 1.85/1.19  #Tautology    : 12
% 1.85/1.19  #SimpNegUnit  : 1
% 1.85/1.19  #BackRed      : 0
% 1.85/1.19  
% 1.85/1.19  #Partial instantiations: 0
% 1.85/1.19  #Strategies tried      : 1
% 1.85/1.19  
% 1.85/1.19  Timing (in seconds)
% 1.85/1.19  ----------------------
% 1.85/1.19  Preprocessing        : 0.29
% 1.85/1.19  Parsing              : 0.16
% 1.85/1.20  CNF conversion       : 0.02
% 1.85/1.20  Main loop            : 0.11
% 1.85/1.20  Inferencing          : 0.05
% 1.85/1.20  Reduction            : 0.03
% 1.85/1.20  Demodulation         : 0.02
% 1.85/1.20  BG Simplification    : 0.01
% 1.85/1.20  Subsumption          : 0.02
% 1.85/1.20  Abstraction          : 0.01
% 1.85/1.20  MUC search           : 0.00
% 1.85/1.20  Cooper               : 0.00
% 1.85/1.20  Total                : 0.42
% 1.85/1.20  Index Insertion      : 0.00
% 1.85/1.20  Index Deletion       : 0.00
% 1.85/1.20  Index Matching       : 0.00
% 1.85/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
