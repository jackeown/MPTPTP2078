%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:34 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   36 (  37 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  37 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_26,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden('#skF_2'(A_31,B_32,C_33),B_32)
      | ~ r2_hidden(A_31,k9_relat_1(C_33,B_32))
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden(A_26,B_27)
      | k4_xboole_0(k1_tarski(A_26),B_27) != k1_tarski(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_113,plain,(
    ! [A_34,C_35] :
      ( ~ r2_hidden(A_34,k9_relat_1(C_35,k1_xboole_0))
      | ~ v1_relat_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_103,c_68])).

tff(c_124,plain,(
    ! [C_36] :
      ( ~ v1_relat_1(C_36)
      | v1_xboole_0(k9_relat_1(C_36,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4,c_113])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_134,plain,(
    ! [C_40] :
      ( k9_relat_1(C_40,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_40) ) ),
    inference(resolution,[status(thm)],[c_124,c_6])).

tff(c_137,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_134])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.46  
% 2.17/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.46  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.17/1.46  
% 2.17/1.46  %Foreground sorts:
% 2.17/1.46  
% 2.17/1.46  
% 2.17/1.46  %Background operators:
% 2.17/1.46  
% 2.17/1.46  
% 2.17/1.46  %Foreground operators:
% 2.17/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.17/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.17/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.17/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.46  
% 2.17/1.48  tff(f_62, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 2.17/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.17/1.48  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.17/1.48  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.17/1.48  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.17/1.48  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.17/1.48  tff(c_26, plain, (k9_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.48  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.48  tff(c_103, plain, (![A_31, B_32, C_33]: (r2_hidden('#skF_2'(A_31, B_32, C_33), B_32) | ~r2_hidden(A_31, k9_relat_1(C_33, B_32)) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.48  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.48  tff(c_63, plain, (![A_26, B_27]: (~r2_hidden(A_26, B_27) | k4_xboole_0(k1_tarski(A_26), B_27)!=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.48  tff(c_68, plain, (![A_26]: (~r2_hidden(A_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_63])).
% 2.17/1.48  tff(c_113, plain, (![A_34, C_35]: (~r2_hidden(A_34, k9_relat_1(C_35, k1_xboole_0)) | ~v1_relat_1(C_35))), inference(resolution, [status(thm)], [c_103, c_68])).
% 2.17/1.48  tff(c_124, plain, (![C_36]: (~v1_relat_1(C_36) | v1_xboole_0(k9_relat_1(C_36, k1_xboole_0)))), inference(resolution, [status(thm)], [c_4, c_113])).
% 2.17/1.48  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.48  tff(c_134, plain, (![C_40]: (k9_relat_1(C_40, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_40))), inference(resolution, [status(thm)], [c_124, c_6])).
% 2.17/1.48  tff(c_137, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_134])).
% 2.17/1.48  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_137])).
% 2.17/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.48  
% 2.17/1.48  Inference rules
% 2.17/1.48  ----------------------
% 2.17/1.48  #Ref     : 0
% 2.17/1.48  #Sup     : 22
% 2.17/1.48  #Fact    : 0
% 2.17/1.48  #Define  : 0
% 2.17/1.48  #Split   : 0
% 2.17/1.48  #Chain   : 0
% 2.17/1.48  #Close   : 0
% 2.17/1.48  
% 2.17/1.48  Ordering : KBO
% 2.17/1.48  
% 2.17/1.48  Simplification rules
% 2.28/1.48  ----------------------
% 2.28/1.48  #Subsume      : 0
% 2.28/1.48  #Demod        : 0
% 2.28/1.48  #Tautology    : 13
% 2.28/1.48  #SimpNegUnit  : 1
% 2.28/1.48  #BackRed      : 0
% 2.28/1.48  
% 2.28/1.48  #Partial instantiations: 0
% 2.28/1.48  #Strategies tried      : 1
% 2.28/1.48  
% 2.28/1.48  Timing (in seconds)
% 2.28/1.48  ----------------------
% 2.28/1.48  Preprocessing        : 0.48
% 2.28/1.48  Parsing              : 0.25
% 2.28/1.48  CNF conversion       : 0.03
% 2.28/1.48  Main loop            : 0.19
% 2.28/1.48  Inferencing          : 0.09
% 2.28/1.48  Reduction            : 0.05
% 2.28/1.48  Demodulation         : 0.03
% 2.28/1.48  BG Simplification    : 0.02
% 2.28/1.49  Subsumption          : 0.03
% 2.28/1.49  Abstraction          : 0.02
% 2.28/1.49  MUC search           : 0.00
% 2.28/1.49  Cooper               : 0.00
% 2.28/1.49  Total                : 0.71
% 2.28/1.49  Index Insertion      : 0.00
% 2.28/1.49  Index Deletion       : 0.00
% 2.28/1.49  Index Matching       : 0.00
% 2.28/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
