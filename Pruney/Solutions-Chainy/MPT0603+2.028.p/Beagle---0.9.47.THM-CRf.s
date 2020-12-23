%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:27 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    4
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_19,plain,(
    ! [A_14] :
      ( k7_relat_1(A_14,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_23,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_19])).

tff(c_16,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ r1_xboole_0(A_18,B_19)
      | ~ r2_hidden(C_20,k3_xboole_0(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_21,B_22] :
      ( ~ r1_xboole_0(A_21,B_22)
      | k3_xboole_0(A_21,B_22) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_48,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_75,plain,(
    ! [C_26,A_27,B_28] :
      ( k7_relat_1(k7_relat_1(C_26,A_27),B_28) = k7_relat_1(C_26,k3_xboole_0(A_27,B_28))
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    k7_relat_1(k7_relat_1('#skF_5','#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_84,plain,
    ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_14])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_23,c_48,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:20:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.19  
% 1.82/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.19  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 1.82/1.19  
% 1.82/1.19  %Foreground sorts:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Background operators:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Foreground operators:
% 1.82/1.19  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.82/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.82/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.82/1.19  
% 1.82/1.20  tff(f_64, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 1.82/1.20  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 1.82/1.20  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.82/1.20  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.82/1.20  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.82/1.20  tff(c_18, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.20  tff(c_19, plain, (![A_14]: (k7_relat_1(A_14, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.20  tff(c_23, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_19])).
% 1.82/1.20  tff(c_16, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.20  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.82/1.20  tff(c_38, plain, (![A_18, B_19, C_20]: (~r1_xboole_0(A_18, B_19) | ~r2_hidden(C_20, k3_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.82/1.20  tff(c_44, plain, (![A_21, B_22]: (~r1_xboole_0(A_21, B_22) | k3_xboole_0(A_21, B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_38])).
% 1.82/1.20  tff(c_48, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_44])).
% 1.82/1.20  tff(c_75, plain, (![C_26, A_27, B_28]: (k7_relat_1(k7_relat_1(C_26, A_27), B_28)=k7_relat_1(C_26, k3_xboole_0(A_27, B_28)) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.82/1.20  tff(c_14, plain, (k7_relat_1(k7_relat_1('#skF_5', '#skF_3'), '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.20  tff(c_84, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_75, c_14])).
% 1.82/1.20  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_23, c_48, c_84])).
% 1.82/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.20  
% 1.82/1.20  Inference rules
% 1.82/1.20  ----------------------
% 1.82/1.20  #Ref     : 0
% 1.82/1.20  #Sup     : 19
% 1.82/1.20  #Fact    : 0
% 1.82/1.20  #Define  : 0
% 1.82/1.20  #Split   : 0
% 1.82/1.20  #Chain   : 0
% 1.82/1.20  #Close   : 0
% 1.82/1.20  
% 1.82/1.20  Ordering : KBO
% 1.82/1.20  
% 1.82/1.20  Simplification rules
% 1.82/1.20  ----------------------
% 1.82/1.20  #Subsume      : 0
% 1.82/1.20  #Demod        : 5
% 1.82/1.20  #Tautology    : 10
% 1.82/1.20  #SimpNegUnit  : 1
% 1.82/1.20  #BackRed      : 0
% 1.82/1.20  
% 1.82/1.20  #Partial instantiations: 0
% 1.82/1.20  #Strategies tried      : 1
% 1.82/1.20  
% 1.82/1.20  Timing (in seconds)
% 1.82/1.20  ----------------------
% 1.82/1.20  Preprocessing        : 0.28
% 1.82/1.20  Parsing              : 0.17
% 1.82/1.20  CNF conversion       : 0.02
% 1.82/1.20  Main loop            : 0.11
% 1.82/1.20  Inferencing          : 0.06
% 1.82/1.20  Reduction            : 0.03
% 1.82/1.20  Demodulation         : 0.02
% 1.82/1.20  BG Simplification    : 0.01
% 1.82/1.20  Subsumption          : 0.01
% 1.82/1.20  Abstraction          : 0.01
% 1.82/1.20  MUC search           : 0.00
% 1.82/1.20  Cooper               : 0.00
% 1.82/1.20  Total                : 0.41
% 1.82/1.20  Index Insertion      : 0.00
% 1.82/1.20  Index Deletion       : 0.00
% 1.82/1.20  Index Matching       : 0.00
% 1.82/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
