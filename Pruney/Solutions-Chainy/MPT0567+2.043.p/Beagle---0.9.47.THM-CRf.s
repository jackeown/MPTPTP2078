%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:20 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_20,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden('#skF_2'(A_21,B_22,C_23),B_22)
      | ~ r2_hidden(A_21,k10_relat_1(C_23,B_22))
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [B_16,A_17] :
      ( ~ r2_hidden(B_16,A_17)
      | k4_xboole_0(A_17,k1_tarski(B_16)) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_45,plain,(
    ! [B_16] : ~ r2_hidden(B_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_40])).

tff(c_85,plain,(
    ! [A_27,C_28] :
      ( ~ r2_hidden(A_27,k10_relat_1(C_28,k1_xboole_0))
      | ~ v1_relat_1(C_28) ) ),
    inference(resolution,[status(thm)],[c_78,c_45])).

tff(c_96,plain,(
    ! [C_29] :
      ( ~ v1_relat_1(C_29)
      | k10_relat_1(C_29,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_85])).

tff(c_99,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_96])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.17  
% 1.66/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.18  %$ r2_hidden > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.66/1.18  
% 1.66/1.18  %Foreground sorts:
% 1.66/1.18  
% 1.66/1.18  
% 1.66/1.18  %Background operators:
% 1.66/1.18  
% 1.66/1.18  
% 1.66/1.18  %Foreground operators:
% 1.66/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.66/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.66/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.66/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.66/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.66/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.18  
% 1.66/1.18  tff(f_58, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 1.66/1.18  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.66/1.18  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.66/1.18  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.66/1.18  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.66/1.18  tff(c_20, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.66/1.18  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.66/1.18  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.18  tff(c_78, plain, (![A_21, B_22, C_23]: (r2_hidden('#skF_2'(A_21, B_22, C_23), B_22) | ~r2_hidden(A_21, k10_relat_1(C_23, B_22)) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.66/1.18  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.18  tff(c_40, plain, (![B_16, A_17]: (~r2_hidden(B_16, A_17) | k4_xboole_0(A_17, k1_tarski(B_16))!=A_17)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.66/1.18  tff(c_45, plain, (![B_16]: (~r2_hidden(B_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_40])).
% 1.66/1.18  tff(c_85, plain, (![A_27, C_28]: (~r2_hidden(A_27, k10_relat_1(C_28, k1_xboole_0)) | ~v1_relat_1(C_28))), inference(resolution, [status(thm)], [c_78, c_45])).
% 1.66/1.18  tff(c_96, plain, (![C_29]: (~v1_relat_1(C_29) | k10_relat_1(C_29, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_85])).
% 1.66/1.18  tff(c_99, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_96])).
% 1.66/1.18  tff(c_103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_99])).
% 1.66/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.18  
% 1.66/1.18  Inference rules
% 1.66/1.18  ----------------------
% 1.66/1.18  #Ref     : 0
% 1.66/1.18  #Sup     : 15
% 1.66/1.19  #Fact    : 0
% 1.66/1.19  #Define  : 0
% 1.66/1.19  #Split   : 0
% 1.66/1.19  #Chain   : 0
% 1.66/1.19  #Close   : 0
% 1.66/1.19  
% 1.66/1.19  Ordering : KBO
% 1.66/1.19  
% 1.66/1.19  Simplification rules
% 1.66/1.19  ----------------------
% 1.66/1.19  #Subsume      : 0
% 1.66/1.19  #Demod        : 0
% 1.66/1.19  #Tautology    : 10
% 1.66/1.19  #SimpNegUnit  : 3
% 1.66/1.19  #BackRed      : 0
% 1.66/1.19  
% 1.66/1.19  #Partial instantiations: 0
% 1.66/1.19  #Strategies tried      : 1
% 1.66/1.19  
% 1.66/1.19  Timing (in seconds)
% 1.66/1.19  ----------------------
% 1.66/1.19  Preprocessing        : 0.25
% 1.66/1.19  Parsing              : 0.13
% 1.66/1.19  CNF conversion       : 0.02
% 1.66/1.19  Main loop            : 0.09
% 1.66/1.19  Inferencing          : 0.04
% 1.76/1.19  Reduction            : 0.02
% 1.76/1.19  Demodulation         : 0.01
% 1.76/1.19  BG Simplification    : 0.01
% 1.76/1.19  Subsumption          : 0.01
% 1.76/1.19  Abstraction          : 0.01
% 1.76/1.19  MUC search           : 0.00
% 1.76/1.19  Cooper               : 0.00
% 1.76/1.19  Total                : 0.36
% 1.76/1.19  Index Insertion      : 0.00
% 1.76/1.19  Index Deletion       : 0.00
% 1.76/1.19  Index Matching       : 0.00
% 1.76/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
