%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:17 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_18,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden('#skF_3'(A_18,B_19,C_20),B_19)
      | ~ r2_hidden(A_18,k10_relat_1(C_20,B_19))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [B_21,A_22,C_23] :
      ( ~ v1_xboole_0(B_21)
      | ~ r2_hidden(A_22,k10_relat_1(C_23,B_21))
      | ~ v1_relat_1(C_23) ) ),
    inference(resolution,[status(thm)],[c_38,c_2])).

tff(c_64,plain,(
    ! [B_27,C_28] :
      ( ~ v1_xboole_0(B_27)
      | ~ v1_relat_1(C_28)
      | k10_relat_1(C_28,B_27) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_43])).

tff(c_68,plain,(
    ! [C_29] :
      ( ~ v1_relat_1(C_29)
      | k10_relat_1(C_29,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_71,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_75,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:58:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.31  
% 1.86/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.31  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 1.86/1.31  
% 1.86/1.31  %Foreground sorts:
% 1.86/1.31  
% 1.86/1.31  
% 1.86/1.31  %Background operators:
% 1.86/1.31  
% 1.86/1.31  
% 1.86/1.31  %Foreground operators:
% 1.86/1.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.86/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.86/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.86/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.86/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.86/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.31  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.86/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.86/1.31  
% 1.86/1.31  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 1.86/1.31  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.86/1.31  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.86/1.31  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.86/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.86/1.31  tff(c_18, plain, (k10_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.31  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.31  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.86/1.31  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.86/1.31  tff(c_38, plain, (![A_18, B_19, C_20]: (r2_hidden('#skF_3'(A_18, B_19, C_20), B_19) | ~r2_hidden(A_18, k10_relat_1(C_20, B_19)) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.86/1.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.31  tff(c_43, plain, (![B_21, A_22, C_23]: (~v1_xboole_0(B_21) | ~r2_hidden(A_22, k10_relat_1(C_23, B_21)) | ~v1_relat_1(C_23))), inference(resolution, [status(thm)], [c_38, c_2])).
% 1.86/1.31  tff(c_64, plain, (![B_27, C_28]: (~v1_xboole_0(B_27) | ~v1_relat_1(C_28) | k10_relat_1(C_28, B_27)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_43])).
% 1.86/1.31  tff(c_68, plain, (![C_29]: (~v1_relat_1(C_29) | k10_relat_1(C_29, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_64])).
% 1.86/1.31  tff(c_71, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_68])).
% 1.86/1.31  tff(c_75, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_71])).
% 1.86/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.31  
% 1.86/1.31  Inference rules
% 1.86/1.31  ----------------------
% 1.86/1.31  #Ref     : 0
% 1.86/1.31  #Sup     : 10
% 1.86/1.31  #Fact    : 0
% 1.86/1.31  #Define  : 0
% 1.86/1.31  #Split   : 0
% 1.86/1.31  #Chain   : 0
% 1.86/1.31  #Close   : 0
% 1.86/1.31  
% 1.86/1.31  Ordering : KBO
% 1.86/1.31  
% 1.86/1.31  Simplification rules
% 1.86/1.31  ----------------------
% 1.86/1.31  #Subsume      : 0
% 1.86/1.31  #Demod        : 0
% 1.86/1.31  #Tautology    : 2
% 1.86/1.31  #SimpNegUnit  : 1
% 1.86/1.31  #BackRed      : 0
% 1.86/1.31  
% 1.86/1.31  #Partial instantiations: 0
% 1.86/1.31  #Strategies tried      : 1
% 1.86/1.31  
% 1.86/1.31  Timing (in seconds)
% 1.86/1.31  ----------------------
% 1.86/1.32  Preprocessing        : 0.37
% 1.86/1.32  Parsing              : 0.23
% 1.86/1.32  CNF conversion       : 0.02
% 1.86/1.32  Main loop            : 0.10
% 1.86/1.32  Inferencing          : 0.05
% 1.86/1.32  Reduction            : 0.02
% 1.86/1.32  Demodulation         : 0.01
% 1.86/1.32  BG Simplification    : 0.01
% 1.86/1.32  Subsumption          : 0.02
% 1.86/1.32  Abstraction          : 0.00
% 1.86/1.32  MUC search           : 0.00
% 1.86/1.32  Cooper               : 0.00
% 1.86/1.32  Total                : 0.49
% 1.86/1.32  Index Insertion      : 0.00
% 1.86/1.32  Index Deletion       : 0.00
% 1.86/1.32  Index Matching       : 0.00
% 1.86/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
