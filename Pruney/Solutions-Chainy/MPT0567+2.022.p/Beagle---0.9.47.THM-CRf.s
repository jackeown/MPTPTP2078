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
% DateTime   : Thu Dec  3 10:01:17 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  42 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(c_28,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_172,plain,(
    ! [A_47,B_48,C_49] :
      ( r2_hidden('#skF_2'(A_47,B_48,C_49),B_48)
      | ~ r2_hidden(A_47,k10_relat_1(C_49,B_48))
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_56,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden(A_26,B_27)
      | ~ r1_xboole_0(k1_tarski(A_26),B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_56])).

tff(c_208,plain,(
    ! [A_52,C_53] :
      ( ~ r2_hidden(A_52,k10_relat_1(C_53,k1_xboole_0))
      | ~ v1_relat_1(C_53) ) ),
    inference(resolution,[status(thm)],[c_172,c_61])).

tff(c_224,plain,(
    ! [C_54,B_55] :
      ( ~ v1_relat_1(C_54)
      | r1_tarski(k10_relat_1(C_54,k1_xboole_0),B_55) ) ),
    inference(resolution,[status(thm)],[c_6,c_208])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_233,plain,(
    ! [C_56,B_57] :
      ( k4_xboole_0(k10_relat_1(C_56,k1_xboole_0),B_57) = k1_xboole_0
      | ~ v1_relat_1(C_56) ) ),
    inference(resolution,[status(thm)],[c_224,c_10])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_267,plain,(
    ! [C_58] :
      ( k10_relat_1(C_58,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_12])).

tff(c_270,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_267])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:48:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.20  
% 1.85/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.20  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.85/1.20  
% 1.85/1.20  %Foreground sorts:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Background operators:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Foreground operators:
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.85/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.85/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.85/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.85/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.85/1.20  
% 1.85/1.21  tff(f_63, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.85/1.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.85/1.21  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.85/1.21  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.85/1.21  tff(f_47, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.85/1.21  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.85/1.21  tff(f_38, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.85/1.21  tff(c_28, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.85/1.21  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.85/1.21  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.21  tff(c_172, plain, (![A_47, B_48, C_49]: (r2_hidden('#skF_2'(A_47, B_48, C_49), B_48) | ~r2_hidden(A_47, k10_relat_1(C_49, B_48)) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.85/1.21  tff(c_14, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.85/1.21  tff(c_56, plain, (![A_26, B_27]: (~r2_hidden(A_26, B_27) | ~r1_xboole_0(k1_tarski(A_26), B_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.85/1.21  tff(c_61, plain, (![A_26]: (~r2_hidden(A_26, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_56])).
% 1.85/1.21  tff(c_208, plain, (![A_52, C_53]: (~r2_hidden(A_52, k10_relat_1(C_53, k1_xboole_0)) | ~v1_relat_1(C_53))), inference(resolution, [status(thm)], [c_172, c_61])).
% 1.85/1.21  tff(c_224, plain, (![C_54, B_55]: (~v1_relat_1(C_54) | r1_tarski(k10_relat_1(C_54, k1_xboole_0), B_55))), inference(resolution, [status(thm)], [c_6, c_208])).
% 1.85/1.21  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.85/1.21  tff(c_233, plain, (![C_56, B_57]: (k4_xboole_0(k10_relat_1(C_56, k1_xboole_0), B_57)=k1_xboole_0 | ~v1_relat_1(C_56))), inference(resolution, [status(thm)], [c_224, c_10])).
% 1.85/1.21  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.21  tff(c_267, plain, (![C_58]: (k10_relat_1(C_58, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_58))), inference(superposition, [status(thm), theory('equality')], [c_233, c_12])).
% 1.85/1.21  tff(c_270, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_267])).
% 1.85/1.21  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_270])).
% 1.85/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.21  
% 1.85/1.21  Inference rules
% 1.85/1.21  ----------------------
% 1.85/1.21  #Ref     : 0
% 1.85/1.21  #Sup     : 51
% 1.85/1.21  #Fact    : 0
% 1.85/1.21  #Define  : 0
% 1.85/1.21  #Split   : 0
% 1.85/1.21  #Chain   : 0
% 1.85/1.21  #Close   : 0
% 1.85/1.21  
% 1.85/1.21  Ordering : KBO
% 1.85/1.21  
% 1.85/1.21  Simplification rules
% 1.85/1.21  ----------------------
% 1.85/1.21  #Subsume      : 2
% 1.85/1.21  #Demod        : 5
% 1.85/1.21  #Tautology    : 32
% 1.85/1.21  #SimpNegUnit  : 1
% 1.85/1.21  #BackRed      : 0
% 1.85/1.21  
% 1.85/1.21  #Partial instantiations: 0
% 1.85/1.21  #Strategies tried      : 1
% 1.85/1.21  
% 1.85/1.21  Timing (in seconds)
% 1.85/1.21  ----------------------
% 1.85/1.21  Preprocessing        : 0.28
% 1.85/1.21  Parsing              : 0.15
% 1.85/1.21  CNF conversion       : 0.02
% 1.85/1.21  Main loop            : 0.16
% 1.85/1.21  Inferencing          : 0.07
% 1.85/1.21  Reduction            : 0.04
% 1.85/1.21  Demodulation         : 0.03
% 1.85/1.21  BG Simplification    : 0.01
% 1.85/1.21  Subsumption          : 0.03
% 1.85/1.21  Abstraction          : 0.01
% 1.85/1.21  MUC search           : 0.00
% 1.85/1.21  Cooper               : 0.00
% 1.85/1.21  Total                : 0.46
% 1.85/1.21  Index Insertion      : 0.00
% 1.85/1.21  Index Deletion       : 0.00
% 1.85/1.21  Index Matching       : 0.00
% 1.85/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
