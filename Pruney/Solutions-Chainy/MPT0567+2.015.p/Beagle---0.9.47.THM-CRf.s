%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:16 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   37 (  38 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  43 expanded)
%              Number of equality atoms :    7 (   8 expanded)
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

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_22,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_2'(A_10,B_11,C_12),B_11)
      | ~ r2_hidden(A_10,k10_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden(A_23,B_24)
      | ~ r1_xboole_0(k1_tarski(A_23),B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_53,plain,(
    ! [A_28] : ~ r2_hidden(A_28,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_42])).

tff(c_65,plain,(
    ! [A_29,C_30] :
      ( ~ r2_hidden(A_29,k10_relat_1(C_30,k1_xboole_0))
      | ~ v1_relat_1(C_30) ) ),
    inference(resolution,[status(thm)],[c_16,c_53])).

tff(c_76,plain,(
    ! [C_31] :
      ( ~ v1_relat_1(C_31)
      | v1_xboole_0(k10_relat_1(C_31,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4,c_65])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,(
    ! [B_19,A_20] :
      ( ~ v1_xboole_0(B_19)
      | B_19 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_6,c_27])).

tff(c_84,plain,(
    ! [C_32] :
      ( k10_relat_1(C_32,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_32) ) ),
    inference(resolution,[status(thm)],[c_76,c_30])).

tff(c_87,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_84])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:24:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.48  
% 2.06/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.48  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.06/1.48  
% 2.06/1.48  %Foreground sorts:
% 2.06/1.48  
% 2.06/1.48  
% 2.06/1.48  %Background operators:
% 2.06/1.48  
% 2.06/1.48  
% 2.06/1.48  %Foreground operators:
% 2.06/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.06/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.06/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.48  
% 2.06/1.50  tff(f_63, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 2.06/1.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.06/1.50  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.06/1.50  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.06/1.50  tff(f_47, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.06/1.50  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.06/1.50  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.06/1.50  tff(c_22, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.06/1.50  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.06/1.50  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.50  tff(c_16, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_2'(A_10, B_11, C_12), B_11) | ~r2_hidden(A_10, k10_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.06/1.50  tff(c_8, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.50  tff(c_42, plain, (![A_23, B_24]: (~r2_hidden(A_23, B_24) | ~r1_xboole_0(k1_tarski(A_23), B_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.50  tff(c_53, plain, (![A_28]: (~r2_hidden(A_28, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_42])).
% 2.06/1.50  tff(c_65, plain, (![A_29, C_30]: (~r2_hidden(A_29, k10_relat_1(C_30, k1_xboole_0)) | ~v1_relat_1(C_30))), inference(resolution, [status(thm)], [c_16, c_53])).
% 2.06/1.50  tff(c_76, plain, (![C_31]: (~v1_relat_1(C_31) | v1_xboole_0(k10_relat_1(C_31, k1_xboole_0)))), inference(resolution, [status(thm)], [c_4, c_65])).
% 2.06/1.50  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.50  tff(c_27, plain, (![B_19, A_20]: (~v1_xboole_0(B_19) | B_19=A_20 | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.50  tff(c_30, plain, (![A_20]: (k1_xboole_0=A_20 | ~v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_6, c_27])).
% 2.06/1.50  tff(c_84, plain, (![C_32]: (k10_relat_1(C_32, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_32))), inference(resolution, [status(thm)], [c_76, c_30])).
% 2.06/1.50  tff(c_87, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_84])).
% 2.06/1.50  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_87])).
% 2.06/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.50  
% 2.06/1.50  Inference rules
% 2.06/1.50  ----------------------
% 2.06/1.50  #Ref     : 0
% 2.06/1.50  #Sup     : 12
% 2.06/1.50  #Fact    : 0
% 2.06/1.50  #Define  : 0
% 2.06/1.50  #Split   : 0
% 2.06/1.50  #Chain   : 0
% 2.06/1.50  #Close   : 0
% 2.06/1.50  
% 2.06/1.50  Ordering : KBO
% 2.06/1.50  
% 2.06/1.50  Simplification rules
% 2.06/1.50  ----------------------
% 2.06/1.50  #Subsume      : 0
% 2.06/1.50  #Demod        : 1
% 2.06/1.50  #Tautology    : 3
% 2.06/1.50  #SimpNegUnit  : 1
% 2.06/1.50  #BackRed      : 0
% 2.06/1.50  
% 2.06/1.50  #Partial instantiations: 0
% 2.06/1.50  #Strategies tried      : 1
% 2.06/1.50  
% 2.06/1.50  Timing (in seconds)
% 2.06/1.50  ----------------------
% 2.15/1.50  Preprocessing        : 0.42
% 2.15/1.50  Parsing              : 0.23
% 2.15/1.50  CNF conversion       : 0.03
% 2.15/1.50  Main loop            : 0.19
% 2.15/1.50  Inferencing          : 0.09
% 2.15/1.50  Reduction            : 0.04
% 2.15/1.50  Demodulation         : 0.03
% 2.15/1.50  BG Simplification    : 0.02
% 2.15/1.50  Subsumption          : 0.03
% 2.15/1.50  Abstraction          : 0.01
% 2.15/1.50  MUC search           : 0.00
% 2.15/1.51  Cooper               : 0.00
% 2.15/1.51  Total                : 0.66
% 2.15/1.51  Index Insertion      : 0.00
% 2.15/1.51  Index Deletion       : 0.00
% 2.15/1.51  Index Matching       : 0.00
% 2.15/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
