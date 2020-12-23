%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:19 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_36,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_193,plain,(
    ! [A_67,B_68,C_69] :
      ( r2_hidden('#skF_2'(A_67,B_68,C_69),B_68)
      | ~ r2_hidden(A_67,k10_relat_1(C_69,B_68))
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_55,plain,(
    ! [C_40,B_41] : ~ r2_hidden(C_40,k4_xboole_0(B_41,k1_tarski(C_40))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_58,plain,(
    ! [C_40] : ~ r2_hidden(C_40,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_55])).

tff(c_204,plain,(
    ! [A_70,C_71] :
      ( ~ r2_hidden(A_70,k10_relat_1(C_71,k1_xboole_0))
      | ~ v1_relat_1(C_71) ) ),
    inference(resolution,[status(thm)],[c_193,c_58])).

tff(c_229,plain,(
    ! [C_77] :
      ( ~ v1_relat_1(C_77)
      | k10_relat_1(C_77,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_204])).

tff(c_232,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_229])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.26  
% 2.00/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.26  %$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.00/1.26  
% 2.00/1.26  %Foreground sorts:
% 2.00/1.26  
% 2.00/1.26  
% 2.00/1.26  %Background operators:
% 2.00/1.26  
% 2.00/1.26  
% 2.00/1.26  %Foreground operators:
% 2.00/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.00/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.00/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.00/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.00/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.00/1.26  
% 2.14/1.27  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 2.14/1.27  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.14/1.27  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.14/1.27  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.14/1.27  tff(f_56, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.14/1.27  tff(c_36, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.27  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.27  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.27  tff(c_193, plain, (![A_67, B_68, C_69]: (r2_hidden('#skF_2'(A_67, B_68, C_69), B_68) | ~r2_hidden(A_67, k10_relat_1(C_69, B_68)) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.14/1.27  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.27  tff(c_55, plain, (![C_40, B_41]: (~r2_hidden(C_40, k4_xboole_0(B_41, k1_tarski(C_40))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.27  tff(c_58, plain, (![C_40]: (~r2_hidden(C_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_55])).
% 2.14/1.27  tff(c_204, plain, (![A_70, C_71]: (~r2_hidden(A_70, k10_relat_1(C_71, k1_xboole_0)) | ~v1_relat_1(C_71))), inference(resolution, [status(thm)], [c_193, c_58])).
% 2.14/1.27  tff(c_229, plain, (![C_77]: (~v1_relat_1(C_77) | k10_relat_1(C_77, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_204])).
% 2.14/1.27  tff(c_232, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_229])).
% 2.14/1.27  tff(c_236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_232])).
% 2.14/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  Inference rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Ref     : 0
% 2.14/1.27  #Sup     : 41
% 2.14/1.27  #Fact    : 0
% 2.14/1.27  #Define  : 0
% 2.14/1.27  #Split   : 0
% 2.14/1.27  #Chain   : 0
% 2.14/1.27  #Close   : 0
% 2.14/1.27  
% 2.14/1.27  Ordering : KBO
% 2.14/1.27  
% 2.14/1.27  Simplification rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Subsume      : 2
% 2.14/1.27  #Demod        : 3
% 2.14/1.27  #Tautology    : 28
% 2.14/1.27  #SimpNegUnit  : 4
% 2.14/1.27  #BackRed      : 0
% 2.14/1.27  
% 2.14/1.27  #Partial instantiations: 0
% 2.14/1.27  #Strategies tried      : 1
% 2.14/1.27  
% 2.14/1.27  Timing (in seconds)
% 2.14/1.27  ----------------------
% 2.14/1.28  Preprocessing        : 0.33
% 2.14/1.28  Parsing              : 0.18
% 2.14/1.28  CNF conversion       : 0.02
% 2.14/1.28  Main loop            : 0.15
% 2.14/1.28  Inferencing          : 0.06
% 2.14/1.28  Reduction            : 0.04
% 2.14/1.28  Demodulation         : 0.03
% 2.14/1.28  BG Simplification    : 0.01
% 2.14/1.28  Subsumption          : 0.02
% 2.14/1.28  Abstraction          : 0.01
% 2.14/1.28  MUC search           : 0.00
% 2.14/1.28  Cooper               : 0.00
% 2.14/1.28  Total                : 0.50
% 2.14/1.28  Index Insertion      : 0.00
% 2.14/1.28  Index Deletion       : 0.00
% 2.14/1.28  Index Matching       : 0.00
% 2.14/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
