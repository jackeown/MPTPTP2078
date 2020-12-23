%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:20 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 (  86 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_24,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden('#skF_3'(A_11,B_12,C_13),B_12)
      | ~ r2_hidden(A_11,k10_relat_1(C_13,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden('#skF_3'(A_11,B_12,C_13),k2_relat_1(C_13))
      | ~ r2_hidden(A_11,k10_relat_1(C_13,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_43,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,B_28)
      | ~ r2_hidden(C_29,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [C_33,B_34,A_35] :
      ( ~ r2_hidden(C_33,B_34)
      | ~ r2_hidden(C_33,A_35)
      | k4_xboole_0(A_35,B_34) != A_35 ) ),
    inference(resolution,[status(thm)],[c_14,c_43])).

tff(c_73,plain,(
    ! [A_39,B_40,A_41] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40),A_41)
      | k4_xboole_0(A_41,A_39) != A_41
      | r1_xboole_0(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_82,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,A_42) != A_42
      | r1_xboole_0(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_91,plain,(
    ! [B_47] : r1_xboole_0(k1_xboole_0,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_82])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_100,plain,(
    ! [C_48,B_49] :
      ( ~ r2_hidden(C_48,B_49)
      | ~ r2_hidden(C_48,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_302,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r2_hidden('#skF_3'(A_84,B_85,C_86),k1_xboole_0)
      | ~ r2_hidden(A_84,k10_relat_1(C_86,B_85))
      | ~ v1_relat_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_22,c_100])).

tff(c_309,plain,(
    ! [A_90,C_91] :
      ( ~ r2_hidden(A_90,k10_relat_1(C_91,k1_xboole_0))
      | ~ v1_relat_1(C_91) ) ),
    inference(resolution,[status(thm)],[c_18,c_302])).

tff(c_335,plain,(
    ! [C_92] :
      ( ~ v1_relat_1(C_92)
      | k10_relat_1(C_92,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_309])).

tff(c_338,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_335])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:12:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.27  
% 2.07/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.27  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.07/1.27  
% 2.07/1.27  %Foreground sorts:
% 2.07/1.27  
% 2.07/1.27  
% 2.07/1.27  %Background operators:
% 2.07/1.27  
% 2.07/1.27  
% 2.07/1.27  %Foreground operators:
% 2.07/1.27  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.07/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.07/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.07/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.07/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.27  
% 2.07/1.28  tff(f_73, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 2.07/1.28  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.07/1.28  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.07/1.28  tff(f_53, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.07/1.28  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.07/1.28  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.07/1.28  tff(c_24, plain, (k10_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.07/1.28  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.07/1.28  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.07/1.28  tff(c_18, plain, (![A_11, B_12, C_13]: (r2_hidden('#skF_3'(A_11, B_12, C_13), B_12) | ~r2_hidden(A_11, k10_relat_1(C_13, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.28  tff(c_22, plain, (![A_11, B_12, C_13]: (r2_hidden('#skF_3'(A_11, B_12, C_13), k2_relat_1(C_13)) | ~r2_hidden(A_11, k10_relat_1(C_13, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.28  tff(c_10, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.07/1.28  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.28  tff(c_14, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.07/1.28  tff(c_43, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, B_28) | ~r2_hidden(C_29, A_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.28  tff(c_48, plain, (![C_33, B_34, A_35]: (~r2_hidden(C_33, B_34) | ~r2_hidden(C_33, A_35) | k4_xboole_0(A_35, B_34)!=A_35)), inference(resolution, [status(thm)], [c_14, c_43])).
% 2.07/1.28  tff(c_73, plain, (![A_39, B_40, A_41]: (~r2_hidden('#skF_1'(A_39, B_40), A_41) | k4_xboole_0(A_41, A_39)!=A_41 | r1_xboole_0(A_39, B_40))), inference(resolution, [status(thm)], [c_6, c_48])).
% 2.07/1.28  tff(c_82, plain, (![A_42, B_43]: (k4_xboole_0(A_42, A_42)!=A_42 | r1_xboole_0(A_42, B_43))), inference(resolution, [status(thm)], [c_6, c_73])).
% 2.07/1.28  tff(c_91, plain, (![B_47]: (r1_xboole_0(k1_xboole_0, B_47))), inference(superposition, [status(thm), theory('equality')], [c_10, c_82])).
% 2.07/1.28  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.28  tff(c_100, plain, (![C_48, B_49]: (~r2_hidden(C_48, B_49) | ~r2_hidden(C_48, k1_xboole_0))), inference(resolution, [status(thm)], [c_91, c_2])).
% 2.07/1.28  tff(c_302, plain, (![A_84, B_85, C_86]: (~r2_hidden('#skF_3'(A_84, B_85, C_86), k1_xboole_0) | ~r2_hidden(A_84, k10_relat_1(C_86, B_85)) | ~v1_relat_1(C_86))), inference(resolution, [status(thm)], [c_22, c_100])).
% 2.07/1.28  tff(c_309, plain, (![A_90, C_91]: (~r2_hidden(A_90, k10_relat_1(C_91, k1_xboole_0)) | ~v1_relat_1(C_91))), inference(resolution, [status(thm)], [c_18, c_302])).
% 2.07/1.28  tff(c_335, plain, (![C_92]: (~v1_relat_1(C_92) | k10_relat_1(C_92, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_309])).
% 2.07/1.28  tff(c_338, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_335])).
% 2.07/1.28  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_338])).
% 2.07/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  Inference rules
% 2.07/1.28  ----------------------
% 2.07/1.28  #Ref     : 0
% 2.07/1.28  #Sup     : 71
% 2.07/1.28  #Fact    : 0
% 2.07/1.28  #Define  : 0
% 2.07/1.28  #Split   : 0
% 2.07/1.28  #Chain   : 0
% 2.07/1.28  #Close   : 0
% 2.07/1.28  
% 2.07/1.28  Ordering : KBO
% 2.07/1.28  
% 2.07/1.28  Simplification rules
% 2.07/1.28  ----------------------
% 2.07/1.28  #Subsume      : 8
% 2.07/1.28  #Demod        : 9
% 2.07/1.28  #Tautology    : 20
% 2.07/1.28  #SimpNegUnit  : 1
% 2.07/1.28  #BackRed      : 0
% 2.07/1.28  
% 2.07/1.28  #Partial instantiations: 0
% 2.07/1.28  #Strategies tried      : 1
% 2.07/1.28  
% 2.07/1.28  Timing (in seconds)
% 2.07/1.28  ----------------------
% 2.07/1.29  Preprocessing        : 0.28
% 2.07/1.29  Parsing              : 0.15
% 2.07/1.29  CNF conversion       : 0.02
% 2.07/1.29  Main loop            : 0.24
% 2.07/1.29  Inferencing          : 0.10
% 2.07/1.29  Reduction            : 0.06
% 2.07/1.29  Demodulation         : 0.04
% 2.07/1.29  BG Simplification    : 0.01
% 2.07/1.29  Subsumption          : 0.06
% 2.07/1.29  Abstraction          : 0.01
% 2.07/1.29  MUC search           : 0.00
% 2.07/1.29  Cooper               : 0.00
% 2.07/1.29  Total                : 0.55
% 2.07/1.29  Index Insertion      : 0.00
% 2.07/1.29  Index Deletion       : 0.00
% 2.07/1.29  Index Matching       : 0.00
% 2.07/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
