%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:19 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

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

tff(c_71,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden('#skF_2'(A_21,B_22,C_23),B_22)
      | ~ r2_hidden(A_21,k10_relat_1(C_23,B_22))
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,(
    ! [A_15,B_16] : ~ r2_hidden(A_15,k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_45])).

tff(c_77,plain,(
    ! [A_24,C_25] :
      ( ~ r2_hidden(A_24,k10_relat_1(C_25,k1_xboole_0))
      | ~ v1_relat_1(C_25) ) ),
    inference(resolution,[status(thm)],[c_71,c_48])).

tff(c_88,plain,(
    ! [C_26] :
      ( ~ v1_relat_1(C_26)
      | k10_relat_1(C_26,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_77])).

tff(c_91,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_88])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:50:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.12  
% 1.78/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.12  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.78/1.12  
% 1.78/1.12  %Foreground sorts:
% 1.78/1.12  
% 1.78/1.12  
% 1.78/1.12  %Background operators:
% 1.78/1.12  
% 1.78/1.12  
% 1.78/1.12  %Foreground operators:
% 1.78/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.78/1.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.78/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.78/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.78/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.12  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.78/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.78/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.12  
% 1.78/1.13  tff(f_58, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 1.78/1.13  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.78/1.13  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.78/1.13  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.78/1.13  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.78/1.13  tff(c_20, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.78/1.13  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.78/1.13  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.13  tff(c_71, plain, (![A_21, B_22, C_23]: (r2_hidden('#skF_2'(A_21, B_22, C_23), B_22) | ~r2_hidden(A_21, k10_relat_1(C_23, B_22)) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.78/1.13  tff(c_6, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.78/1.13  tff(c_45, plain, (![A_15, B_16]: (~r2_hidden(A_15, k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.78/1.13  tff(c_48, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_45])).
% 1.78/1.13  tff(c_77, plain, (![A_24, C_25]: (~r2_hidden(A_24, k10_relat_1(C_25, k1_xboole_0)) | ~v1_relat_1(C_25))), inference(resolution, [status(thm)], [c_71, c_48])).
% 1.78/1.13  tff(c_88, plain, (![C_26]: (~v1_relat_1(C_26) | k10_relat_1(C_26, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_77])).
% 1.78/1.13  tff(c_91, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_88])).
% 1.78/1.13  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_91])).
% 1.78/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.13  
% 1.78/1.13  Inference rules
% 1.78/1.13  ----------------------
% 1.78/1.13  #Ref     : 0
% 1.78/1.13  #Sup     : 15
% 1.78/1.13  #Fact    : 0
% 1.78/1.13  #Define  : 0
% 1.78/1.13  #Split   : 0
% 1.78/1.13  #Chain   : 0
% 1.78/1.13  #Close   : 0
% 1.78/1.13  
% 1.78/1.13  Ordering : KBO
% 1.78/1.13  
% 1.78/1.13  Simplification rules
% 1.78/1.13  ----------------------
% 1.78/1.13  #Subsume      : 1
% 1.78/1.13  #Demod        : 0
% 1.78/1.13  #Tautology    : 9
% 1.78/1.13  #SimpNegUnit  : 1
% 1.78/1.13  #BackRed      : 0
% 1.78/1.13  
% 1.78/1.13  #Partial instantiations: 0
% 1.78/1.13  #Strategies tried      : 1
% 1.78/1.13  
% 1.78/1.13  Timing (in seconds)
% 1.78/1.13  ----------------------
% 1.78/1.13  Preprocessing        : 0.27
% 1.78/1.13  Parsing              : 0.14
% 1.78/1.13  CNF conversion       : 0.02
% 1.78/1.13  Main loop            : 0.11
% 1.78/1.14  Inferencing          : 0.05
% 1.78/1.14  Reduction            : 0.03
% 1.78/1.14  Demodulation         : 0.01
% 1.78/1.14  BG Simplification    : 0.01
% 1.78/1.14  Subsumption          : 0.02
% 1.78/1.14  Abstraction          : 0.00
% 1.78/1.14  MUC search           : 0.00
% 1.78/1.14  Cooper               : 0.00
% 1.78/1.14  Total                : 0.40
% 1.78/1.14  Index Insertion      : 0.00
% 1.78/1.14  Index Deletion       : 0.00
% 1.78/1.14  Index Matching       : 0.00
% 1.78/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
