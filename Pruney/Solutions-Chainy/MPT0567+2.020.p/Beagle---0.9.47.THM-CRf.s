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

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 (  68 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k5_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_24,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden('#skF_3'(A_14,B_15,C_16),B_15)
      | ~ r2_hidden(A_14,k10_relat_1(C_16,B_15))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_43,plain,(
    ! [A_25,B_26] : r1_xboole_0(k3_xboole_0(A_25,B_26),k5_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    ! [A_13] : r1_xboole_0(k3_xboole_0(A_13,k1_xboole_0),A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_43])).

tff(c_48,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_33,B_34] :
      ( ~ r1_xboole_0(A_33,B_34)
      | v1_xboole_0(k3_xboole_0(A_33,B_34)) ) ),
    inference(resolution,[status(thm)],[c_4,c_48])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_xboole_0(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_63,c_6])).

tff(c_82,plain,(
    ! [A_39] : k3_xboole_0(k3_xboole_0(A_39,k1_xboole_0),A_39) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    ! [A_39,C_10] :
      ( ~ r1_xboole_0(k3_xboole_0(A_39,k1_xboole_0),A_39)
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10])).

tff(c_137,plain,(
    ! [C_43] : ~ r2_hidden(C_43,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_100])).

tff(c_221,plain,(
    ! [A_51,C_52] :
      ( ~ r2_hidden(A_51,k10_relat_1(C_52,k1_xboole_0))
      | ~ v1_relat_1(C_52) ) ),
    inference(resolution,[status(thm)],[c_18,c_137])).

tff(c_237,plain,(
    ! [C_53] :
      ( ~ v1_relat_1(C_53)
      | v1_xboole_0(k10_relat_1(C_53,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4,c_221])).

tff(c_242,plain,(
    ! [C_54] :
      ( k10_relat_1(C_54,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_54) ) ),
    inference(resolution,[status(thm)],[c_237,c_6])).

tff(c_245,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_242])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:35:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.20  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k5_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 1.96/1.20  
% 1.96/1.20  %Foreground sorts:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Background operators:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Foreground operators:
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.96/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.96/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.96/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.96/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.96/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.20  
% 1.96/1.21  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.96/1.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.96/1.21  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.96/1.21  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.96/1.21  tff(f_51, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_xboole_1)).
% 1.96/1.21  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.96/1.21  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.96/1.21  tff(c_24, plain, (k10_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.96/1.21  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.96/1.21  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.21  tff(c_18, plain, (![A_14, B_15, C_16]: (r2_hidden('#skF_3'(A_14, B_15, C_16), B_15) | ~r2_hidden(A_14, k10_relat_1(C_16, B_15)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.21  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.96/1.21  tff(c_43, plain, (![A_25, B_26]: (r1_xboole_0(k3_xboole_0(A_25, B_26), k5_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.21  tff(c_46, plain, (![A_13]: (r1_xboole_0(k3_xboole_0(A_13, k1_xboole_0), A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_43])).
% 1.96/1.21  tff(c_48, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.96/1.21  tff(c_63, plain, (![A_33, B_34]: (~r1_xboole_0(A_33, B_34) | v1_xboole_0(k3_xboole_0(A_33, B_34)))), inference(resolution, [status(thm)], [c_4, c_48])).
% 1.96/1.21  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.21  tff(c_73, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_xboole_0(A_37, B_38))), inference(resolution, [status(thm)], [c_63, c_6])).
% 1.96/1.21  tff(c_82, plain, (![A_39]: (k3_xboole_0(k3_xboole_0(A_39, k1_xboole_0), A_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_73])).
% 1.96/1.21  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.96/1.21  tff(c_100, plain, (![A_39, C_10]: (~r1_xboole_0(k3_xboole_0(A_39, k1_xboole_0), A_39) | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_82, c_10])).
% 1.96/1.21  tff(c_137, plain, (![C_43]: (~r2_hidden(C_43, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_100])).
% 1.96/1.21  tff(c_221, plain, (![A_51, C_52]: (~r2_hidden(A_51, k10_relat_1(C_52, k1_xboole_0)) | ~v1_relat_1(C_52))), inference(resolution, [status(thm)], [c_18, c_137])).
% 1.96/1.21  tff(c_237, plain, (![C_53]: (~v1_relat_1(C_53) | v1_xboole_0(k10_relat_1(C_53, k1_xboole_0)))), inference(resolution, [status(thm)], [c_4, c_221])).
% 1.96/1.21  tff(c_242, plain, (![C_54]: (k10_relat_1(C_54, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_54))), inference(resolution, [status(thm)], [c_237, c_6])).
% 1.96/1.21  tff(c_245, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_242])).
% 1.96/1.21  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_245])).
% 1.96/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  
% 1.96/1.21  Inference rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Ref     : 0
% 1.96/1.21  #Sup     : 47
% 1.96/1.21  #Fact    : 0
% 1.96/1.21  #Define  : 0
% 1.96/1.21  #Split   : 0
% 1.96/1.21  #Chain   : 0
% 1.96/1.21  #Close   : 0
% 1.96/1.21  
% 1.96/1.21  Ordering : KBO
% 1.96/1.21  
% 1.96/1.21  Simplification rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Subsume      : 1
% 1.96/1.21  #Demod        : 15
% 1.96/1.21  #Tautology    : 20
% 1.96/1.21  #SimpNegUnit  : 2
% 1.96/1.21  #BackRed      : 0
% 1.96/1.21  
% 1.96/1.21  #Partial instantiations: 0
% 1.96/1.21  #Strategies tried      : 1
% 1.96/1.21  
% 1.96/1.21  Timing (in seconds)
% 1.96/1.21  ----------------------
% 1.96/1.21  Preprocessing        : 0.28
% 1.96/1.21  Parsing              : 0.16
% 1.96/1.21  CNF conversion       : 0.02
% 1.96/1.21  Main loop            : 0.17
% 1.96/1.21  Inferencing          : 0.08
% 1.96/1.21  Reduction            : 0.04
% 1.96/1.21  Demodulation         : 0.03
% 1.96/1.21  BG Simplification    : 0.01
% 1.96/1.21  Subsumption          : 0.03
% 1.96/1.21  Abstraction          : 0.01
% 1.96/1.21  MUC search           : 0.00
% 1.96/1.21  Cooper               : 0.00
% 1.96/1.21  Total                : 0.47
% 1.96/1.21  Index Insertion      : 0.00
% 1.96/1.21  Index Deletion       : 0.00
% 1.96/1.21  Index Matching       : 0.00
% 1.96/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
