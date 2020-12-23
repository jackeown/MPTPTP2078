%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:17 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  49 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

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

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_50,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_26,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [A_41,B_42,C_43] :
      ( r2_hidden('#skF_3'(A_41,B_42,C_43),B_42)
      | ~ r2_hidden(A_41,k10_relat_1(C_43,B_42))
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_53,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    ! [A_10,C_30] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_30,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_53])).

tff(c_63,plain,(
    ! [C_30] : ~ r2_hidden(C_30,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_60])).

tff(c_136,plain,(
    ! [A_46,C_47] :
      ( ~ r2_hidden(A_46,k10_relat_1(C_47,k1_xboole_0))
      | ~ v1_relat_1(C_47) ) ),
    inference(resolution,[status(thm)],[c_111,c_63])).

tff(c_147,plain,(
    ! [C_48] :
      ( ~ v1_relat_1(C_48)
      | v1_xboole_0(k10_relat_1(C_48,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [B_24,A_25] :
      ( ~ v1_xboole_0(B_24)
      | B_24 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_41,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_163,plain,(
    ! [C_52] :
      ( k10_relat_1(C_52,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_52) ) ),
    inference(resolution,[status(thm)],[c_147,c_41])).

tff(c_166,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_163])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.22  
% 1.78/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.22  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 1.78/1.22  
% 1.78/1.22  %Foreground sorts:
% 1.78/1.22  
% 1.78/1.22  
% 1.78/1.22  %Background operators:
% 1.78/1.22  
% 1.78/1.22  
% 1.78/1.22  %Foreground operators:
% 1.78/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.78/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.78/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.78/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.78/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.78/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.78/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.78/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.78/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.78/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.78/1.22  
% 1.97/1.23  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 1.97/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.97/1.23  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.97/1.23  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.97/1.23  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.97/1.23  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.97/1.23  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.97/1.23  tff(f_58, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.97/1.23  tff(c_26, plain, (k10_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.97/1.23  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.97/1.23  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.23  tff(c_111, plain, (![A_41, B_42, C_43]: (r2_hidden('#skF_3'(A_41, B_42, C_43), B_42) | ~r2_hidden(A_41, k10_relat_1(C_43, B_42)) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.97/1.23  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.23  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.23  tff(c_53, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.97/1.23  tff(c_60, plain, (![A_10, C_30]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_53])).
% 1.97/1.23  tff(c_63, plain, (![C_30]: (~r2_hidden(C_30, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_60])).
% 1.97/1.23  tff(c_136, plain, (![A_46, C_47]: (~r2_hidden(A_46, k10_relat_1(C_47, k1_xboole_0)) | ~v1_relat_1(C_47))), inference(resolution, [status(thm)], [c_111, c_63])).
% 1.97/1.23  tff(c_147, plain, (![C_48]: (~v1_relat_1(C_48) | v1_xboole_0(k10_relat_1(C_48, k1_xboole_0)))), inference(resolution, [status(thm)], [c_4, c_136])).
% 1.97/1.23  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.23  tff(c_38, plain, (![B_24, A_25]: (~v1_xboole_0(B_24) | B_24=A_25 | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.97/1.23  tff(c_41, plain, (![A_25]: (k1_xboole_0=A_25 | ~v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_6, c_38])).
% 1.97/1.23  tff(c_163, plain, (![C_52]: (k10_relat_1(C_52, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_52))), inference(resolution, [status(thm)], [c_147, c_41])).
% 1.97/1.23  tff(c_166, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_163])).
% 1.97/1.23  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_166])).
% 1.97/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.23  
% 1.97/1.23  Inference rules
% 1.97/1.23  ----------------------
% 1.97/1.23  #Ref     : 0
% 1.97/1.23  #Sup     : 29
% 1.97/1.23  #Fact    : 0
% 1.97/1.23  #Define  : 0
% 1.97/1.23  #Split   : 0
% 1.97/1.23  #Chain   : 0
% 1.97/1.23  #Close   : 0
% 1.97/1.23  
% 1.97/1.23  Ordering : KBO
% 1.97/1.23  
% 1.97/1.23  Simplification rules
% 1.97/1.23  ----------------------
% 1.97/1.23  #Subsume      : 1
% 1.97/1.23  #Demod        : 8
% 1.97/1.23  #Tautology    : 11
% 1.97/1.23  #SimpNegUnit  : 2
% 1.97/1.23  #BackRed      : 0
% 1.97/1.23  
% 1.97/1.23  #Partial instantiations: 0
% 1.97/1.23  #Strategies tried      : 1
% 1.97/1.23  
% 1.97/1.23  Timing (in seconds)
% 1.97/1.23  ----------------------
% 1.97/1.24  Preprocessing        : 0.28
% 1.97/1.24  Parsing              : 0.16
% 1.97/1.24  CNF conversion       : 0.02
% 1.97/1.24  Main loop            : 0.15
% 1.97/1.24  Inferencing          : 0.07
% 1.97/1.24  Reduction            : 0.04
% 1.97/1.24  Demodulation         : 0.03
% 1.97/1.24  BG Simplification    : 0.01
% 1.97/1.24  Subsumption          : 0.02
% 1.97/1.24  Abstraction          : 0.01
% 1.97/1.24  MUC search           : 0.00
% 1.97/1.24  Cooper               : 0.00
% 1.97/1.24  Total                : 0.46
% 1.97/1.24  Index Insertion      : 0.00
% 1.97/1.24  Index Deletion       : 0.00
% 1.97/1.24  Index Matching       : 0.00
% 1.97/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
