%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:20 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_18,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden('#skF_2'(A_23,B_24,C_25),B_24)
      | ~ r2_hidden(A_23,k10_relat_1(C_25,B_24))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_19,C_20,B_21] :
      ( ~ r2_hidden(A_19,C_20)
      | ~ r1_xboole_0(k2_tarski(A_19,B_21),C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_37,plain,(
    ! [A_19] : ~ r2_hidden(A_19,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_32])).

tff(c_51,plain,(
    ! [A_26,C_27] :
      ( ~ r2_hidden(A_26,k10_relat_1(C_27,k1_xboole_0))
      | ~ v1_relat_1(C_27) ) ),
    inference(resolution,[status(thm)],[c_45,c_37])).

tff(c_63,plain,(
    ! [C_31] :
      ( ~ v1_relat_1(C_31)
      | k10_relat_1(C_31,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_51])).

tff(c_66,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_63])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:16:00 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.08  
% 1.68/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.09  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.68/1.09  
% 1.68/1.09  %Foreground sorts:
% 1.68/1.09  
% 1.68/1.09  
% 1.68/1.09  %Background operators:
% 1.68/1.09  
% 1.68/1.09  
% 1.68/1.09  %Foreground operators:
% 1.68/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.09  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.68/1.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.68/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.68/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.68/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.68/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.68/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.09  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.68/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.09  
% 1.68/1.09  tff(f_58, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.68/1.09  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.68/1.09  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.68/1.09  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.68/1.09  tff(f_42, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.68/1.09  tff(c_18, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.68/1.09  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.68/1.09  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.09  tff(c_45, plain, (![A_23, B_24, C_25]: (r2_hidden('#skF_2'(A_23, B_24, C_25), B_24) | ~r2_hidden(A_23, k10_relat_1(C_25, B_24)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.68/1.09  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.68/1.09  tff(c_32, plain, (![A_19, C_20, B_21]: (~r2_hidden(A_19, C_20) | ~r1_xboole_0(k2_tarski(A_19, B_21), C_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.68/1.09  tff(c_37, plain, (![A_19]: (~r2_hidden(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_32])).
% 1.68/1.09  tff(c_51, plain, (![A_26, C_27]: (~r2_hidden(A_26, k10_relat_1(C_27, k1_xboole_0)) | ~v1_relat_1(C_27))), inference(resolution, [status(thm)], [c_45, c_37])).
% 1.68/1.09  tff(c_63, plain, (![C_31]: (~v1_relat_1(C_31) | k10_relat_1(C_31, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_51])).
% 1.68/1.09  tff(c_66, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_63])).
% 1.68/1.09  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_66])).
% 1.68/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.09  
% 1.68/1.09  Inference rules
% 1.68/1.09  ----------------------
% 1.68/1.09  #Ref     : 0
% 1.68/1.09  #Sup     : 8
% 1.68/1.09  #Fact    : 0
% 1.68/1.09  #Define  : 0
% 1.68/1.09  #Split   : 0
% 1.68/1.09  #Chain   : 0
% 1.68/1.09  #Close   : 0
% 1.68/1.09  
% 1.68/1.09  Ordering : KBO
% 1.68/1.09  
% 1.68/1.09  Simplification rules
% 1.68/1.09  ----------------------
% 1.68/1.09  #Subsume      : 0
% 1.68/1.09  #Demod        : 0
% 1.68/1.09  #Tautology    : 3
% 1.68/1.09  #SimpNegUnit  : 1
% 1.68/1.09  #BackRed      : 0
% 1.68/1.09  
% 1.68/1.09  #Partial instantiations: 0
% 1.68/1.09  #Strategies tried      : 1
% 1.68/1.09  
% 1.68/1.09  Timing (in seconds)
% 1.68/1.09  ----------------------
% 1.68/1.10  Preprocessing        : 0.28
% 1.68/1.10  Parsing              : 0.15
% 1.68/1.10  CNF conversion       : 0.02
% 1.68/1.10  Main loop            : 0.08
% 1.68/1.10  Inferencing          : 0.04
% 1.68/1.10  Reduction            : 0.02
% 1.68/1.10  Demodulation         : 0.01
% 1.68/1.10  BG Simplification    : 0.01
% 1.68/1.10  Subsumption          : 0.01
% 1.68/1.10  Abstraction          : 0.01
% 1.68/1.10  MUC search           : 0.00
% 1.68/1.10  Cooper               : 0.00
% 1.68/1.10  Total                : 0.38
% 1.68/1.10  Index Insertion      : 0.00
% 1.68/1.10  Index Deletion       : 0.00
% 1.68/1.10  Index Matching       : 0.00
% 1.68/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
