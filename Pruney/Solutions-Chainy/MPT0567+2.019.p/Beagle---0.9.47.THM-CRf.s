%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:17 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  37 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_20,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden('#skF_2'(A_23,B_24,C_25),B_24)
      | ~ r2_hidden(A_23,k10_relat_1(C_25,B_24))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden(A_20,B_21)
      | ~ r1_xboole_0(k1_tarski(A_20),B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ! [A_20] : ~ r2_hidden(A_20,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_31])).

tff(c_58,plain,(
    ! [A_26,C_27] :
      ( ~ r2_hidden(A_26,k10_relat_1(C_27,k1_xboole_0))
      | ~ v1_relat_1(C_27) ) ),
    inference(resolution,[status(thm)],[c_48,c_36])).

tff(c_69,plain,(
    ! [C_28] :
      ( ~ v1_relat_1(C_28)
      | v1_xboole_0(k10_relat_1(C_28,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [C_29] :
      ( k10_relat_1(C_29,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_29) ) ),
    inference(resolution,[status(thm)],[c_69,c_6])).

tff(c_77,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_74])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.52  
% 2.19/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.53  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.19/1.53  
% 2.19/1.53  %Foreground sorts:
% 2.19/1.53  
% 2.19/1.53  
% 2.19/1.53  %Background operators:
% 2.19/1.53  
% 2.19/1.53  
% 2.19/1.53  %Foreground operators:
% 2.19/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.19/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.19/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.19/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.53  
% 2.19/1.54  tff(f_58, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 2.19/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.19/1.54  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.19/1.54  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.19/1.54  tff(f_42, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.19/1.54  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.19/1.54  tff(c_20, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.54  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.54  tff(c_48, plain, (![A_23, B_24, C_25]: (r2_hidden('#skF_2'(A_23, B_24, C_25), B_24) | ~r2_hidden(A_23, k10_relat_1(C_25, B_24)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.54  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.54  tff(c_31, plain, (![A_20, B_21]: (~r2_hidden(A_20, B_21) | ~r1_xboole_0(k1_tarski(A_20), B_21))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.19/1.54  tff(c_36, plain, (![A_20]: (~r2_hidden(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_31])).
% 2.19/1.54  tff(c_58, plain, (![A_26, C_27]: (~r2_hidden(A_26, k10_relat_1(C_27, k1_xboole_0)) | ~v1_relat_1(C_27))), inference(resolution, [status(thm)], [c_48, c_36])).
% 2.19/1.54  tff(c_69, plain, (![C_28]: (~v1_relat_1(C_28) | v1_xboole_0(k10_relat_1(C_28, k1_xboole_0)))), inference(resolution, [status(thm)], [c_4, c_58])).
% 2.19/1.54  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.54  tff(c_74, plain, (![C_29]: (k10_relat_1(C_29, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_29))), inference(resolution, [status(thm)], [c_69, c_6])).
% 2.19/1.54  tff(c_77, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_74])).
% 2.19/1.54  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_77])).
% 2.19/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.54  
% 2.19/1.54  Inference rules
% 2.19/1.54  ----------------------
% 2.19/1.54  #Ref     : 0
% 2.19/1.54  #Sup     : 10
% 2.19/1.54  #Fact    : 0
% 2.19/1.54  #Define  : 0
% 2.19/1.54  #Split   : 0
% 2.19/1.54  #Chain   : 0
% 2.19/1.54  #Close   : 0
% 2.19/1.54  
% 2.19/1.54  Ordering : KBO
% 2.19/1.54  
% 2.19/1.54  Simplification rules
% 2.19/1.54  ----------------------
% 2.19/1.54  #Subsume      : 0
% 2.19/1.54  #Demod        : 0
% 2.19/1.54  #Tautology    : 2
% 2.19/1.54  #SimpNegUnit  : 1
% 2.19/1.54  #BackRed      : 0
% 2.19/1.54  
% 2.19/1.54  #Partial instantiations: 0
% 2.19/1.54  #Strategies tried      : 1
% 2.19/1.54  
% 2.19/1.54  Timing (in seconds)
% 2.19/1.54  ----------------------
% 2.19/1.55  Preprocessing        : 0.43
% 2.19/1.55  Parsing              : 0.23
% 2.19/1.55  CNF conversion       : 0.03
% 2.19/1.55  Main loop            : 0.19
% 2.19/1.55  Inferencing          : 0.08
% 2.19/1.55  Reduction            : 0.04
% 2.19/1.55  Demodulation         : 0.02
% 2.19/1.55  BG Simplification    : 0.02
% 2.19/1.55  Subsumption          : 0.03
% 2.19/1.55  Abstraction          : 0.01
% 2.19/1.55  MUC search           : 0.00
% 2.19/1.55  Cooper               : 0.00
% 2.19/1.55  Total                : 0.66
% 2.19/1.55  Index Insertion      : 0.00
% 2.19/1.55  Index Deletion       : 0.00
% 2.19/1.55  Index Matching       : 0.00
% 2.19/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
