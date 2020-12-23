%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:19 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_16,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | ~ r2_hidden(A_6,k10_relat_1(C_8,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_21,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden(A_14,B_15)
      | ~ r1_xboole_0(k1_tarski(A_14),B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_28,plain,(
    ! [A_19] : ~ r2_hidden(A_19,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_21])).

tff(c_40,plain,(
    ! [A_20,C_21] :
      ( ~ r2_hidden(A_20,k10_relat_1(C_21,k1_xboole_0))
      | ~ v1_relat_1(C_21) ) ),
    inference(resolution,[status(thm)],[c_10,c_28])).

tff(c_51,plain,(
    ! [C_22] :
      ( ~ v1_relat_1(C_22)
      | k10_relat_1(C_22,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_40])).

tff(c_54,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_51])).

tff(c_58,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:51:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.16  
% 1.60/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.16  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.60/1.16  
% 1.60/1.16  %Foreground sorts:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Background operators:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Foreground operators:
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.60/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.60/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.60/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.60/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.60/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.16  
% 1.60/1.17  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 1.60/1.17  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.60/1.17  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.60/1.17  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.60/1.17  tff(f_40, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.60/1.17  tff(c_16, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.60/1.17  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.60/1.17  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.60/1.17  tff(c_10, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | ~r2_hidden(A_6, k10_relat_1(C_8, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.60/1.17  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.60/1.17  tff(c_21, plain, (![A_14, B_15]: (~r2_hidden(A_14, B_15) | ~r1_xboole_0(k1_tarski(A_14), B_15))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.60/1.17  tff(c_28, plain, (![A_19]: (~r2_hidden(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_21])).
% 1.60/1.17  tff(c_40, plain, (![A_20, C_21]: (~r2_hidden(A_20, k10_relat_1(C_21, k1_xboole_0)) | ~v1_relat_1(C_21))), inference(resolution, [status(thm)], [c_10, c_28])).
% 1.60/1.17  tff(c_51, plain, (![C_22]: (~v1_relat_1(C_22) | k10_relat_1(C_22, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_40])).
% 1.60/1.17  tff(c_54, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_51])).
% 1.60/1.17  tff(c_58, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_54])).
% 1.60/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.17  
% 1.60/1.17  Inference rules
% 1.60/1.17  ----------------------
% 1.60/1.17  #Ref     : 0
% 1.60/1.17  #Sup     : 6
% 1.60/1.17  #Fact    : 0
% 1.60/1.17  #Define  : 0
% 1.60/1.17  #Split   : 0
% 1.60/1.17  #Chain   : 0
% 1.60/1.17  #Close   : 0
% 1.60/1.17  
% 1.60/1.17  Ordering : KBO
% 1.60/1.17  
% 1.60/1.17  Simplification rules
% 1.60/1.17  ----------------------
% 1.60/1.17  #Subsume      : 0
% 1.60/1.17  #Demod        : 0
% 1.60/1.17  #Tautology    : 1
% 1.60/1.17  #SimpNegUnit  : 1
% 1.60/1.17  #BackRed      : 0
% 1.60/1.17  
% 1.60/1.17  #Partial instantiations: 0
% 1.60/1.17  #Strategies tried      : 1
% 1.60/1.17  
% 1.60/1.17  Timing (in seconds)
% 1.60/1.17  ----------------------
% 1.60/1.17  Preprocessing        : 0.28
% 1.60/1.17  Parsing              : 0.15
% 1.60/1.17  CNF conversion       : 0.02
% 1.60/1.17  Main loop            : 0.09
% 1.60/1.17  Inferencing          : 0.04
% 1.60/1.17  Reduction            : 0.02
% 1.60/1.17  Demodulation         : 0.01
% 1.60/1.17  BG Simplification    : 0.01
% 1.60/1.17  Subsumption          : 0.01
% 1.60/1.17  Abstraction          : 0.00
% 1.60/1.17  MUC search           : 0.00
% 1.60/1.17  Cooper               : 0.00
% 1.60/1.17  Total                : 0.39
% 1.60/1.17  Index Insertion      : 0.00
% 1.60/1.17  Index Deletion       : 0.00
% 1.60/1.17  Index Matching       : 0.00
% 1.60/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
