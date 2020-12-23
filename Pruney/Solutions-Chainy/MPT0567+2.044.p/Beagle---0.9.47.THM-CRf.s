%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:20 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_18,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden('#skF_3'(A_26,B_27,C_28),B_27)
      | ~ r2_hidden(A_26,k10_relat_1(C_28,B_27))
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_23,plain,(
    ! [A_17,B_18,C_19] :
      ( ~ r1_xboole_0(A_17,B_18)
      | ~ r2_hidden(C_19,k3_xboole_0(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( ~ r1_xboole_0(A_22,B_23)
      | k3_xboole_0(A_22,B_23) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_23])).

tff(c_39,plain,(
    ! [A_24] : k3_xboole_0(A_24,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_34])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [A_24,C_5] :
      ( ~ r1_xboole_0(A_24,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_4])).

tff(c_53,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_47])).

tff(c_73,plain,(
    ! [A_29,C_30] :
      ( ~ r2_hidden(A_29,k10_relat_1(C_30,k1_xboole_0))
      | ~ v1_relat_1(C_30) ) ),
    inference(resolution,[status(thm)],[c_62,c_53])).

tff(c_84,plain,(
    ! [C_31] :
      ( ~ v1_relat_1(C_31)
      | k10_relat_1(C_31,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_87,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_84])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:33:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.16  
% 1.64/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.16  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.64/1.16  
% 1.64/1.16  %Foreground sorts:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Background operators:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Foreground operators:
% 1.64/1.16  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.64/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.64/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.64/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.64/1.16  
% 1.64/1.17  tff(f_65, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 1.64/1.17  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.64/1.17  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.64/1.17  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.64/1.17  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.64/1.17  tff(c_18, plain, (k10_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.64/1.17  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.64/1.17  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.17  tff(c_62, plain, (![A_26, B_27, C_28]: (r2_hidden('#skF_3'(A_26, B_27, C_28), B_27) | ~r2_hidden(A_26, k10_relat_1(C_28, B_27)) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.64/1.17  tff(c_8, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.64/1.17  tff(c_23, plain, (![A_17, B_18, C_19]: (~r1_xboole_0(A_17, B_18) | ~r2_hidden(C_19, k3_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.17  tff(c_34, plain, (![A_22, B_23]: (~r1_xboole_0(A_22, B_23) | k3_xboole_0(A_22, B_23)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_23])).
% 1.64/1.17  tff(c_39, plain, (![A_24]: (k3_xboole_0(A_24, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_34])).
% 1.64/1.17  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.17  tff(c_47, plain, (![A_24, C_5]: (~r1_xboole_0(A_24, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_39, c_4])).
% 1.64/1.17  tff(c_53, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_47])).
% 1.64/1.17  tff(c_73, plain, (![A_29, C_30]: (~r2_hidden(A_29, k10_relat_1(C_30, k1_xboole_0)) | ~v1_relat_1(C_30))), inference(resolution, [status(thm)], [c_62, c_53])).
% 1.64/1.17  tff(c_84, plain, (![C_31]: (~v1_relat_1(C_31) | k10_relat_1(C_31, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_73])).
% 1.64/1.17  tff(c_87, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_84])).
% 1.64/1.17  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_87])).
% 1.64/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.17  
% 1.64/1.17  Inference rules
% 1.64/1.17  ----------------------
% 1.64/1.17  #Ref     : 0
% 1.64/1.17  #Sup     : 13
% 1.64/1.17  #Fact    : 0
% 1.64/1.17  #Define  : 0
% 1.64/1.17  #Split   : 0
% 1.64/1.17  #Chain   : 0
% 1.64/1.17  #Close   : 0
% 1.64/1.17  
% 1.64/1.17  Ordering : KBO
% 1.64/1.17  
% 1.64/1.17  Simplification rules
% 1.64/1.17  ----------------------
% 1.64/1.17  #Subsume      : 0
% 1.64/1.17  #Demod        : 2
% 1.64/1.17  #Tautology    : 5
% 1.64/1.17  #SimpNegUnit  : 1
% 1.64/1.17  #BackRed      : 0
% 1.64/1.17  
% 1.64/1.17  #Partial instantiations: 0
% 1.64/1.17  #Strategies tried      : 1
% 1.64/1.17  
% 1.64/1.17  Timing (in seconds)
% 1.64/1.17  ----------------------
% 1.64/1.17  Preprocessing        : 0.27
% 1.64/1.17  Parsing              : 0.16
% 1.64/1.17  CNF conversion       : 0.02
% 1.64/1.17  Main loop            : 0.10
% 1.64/1.17  Inferencing          : 0.05
% 1.64/1.17  Reduction            : 0.02
% 1.64/1.17  Demodulation         : 0.02
% 1.64/1.17  BG Simplification    : 0.01
% 1.64/1.17  Subsumption          : 0.01
% 1.64/1.17  Abstraction          : 0.00
% 1.64/1.17  MUC search           : 0.00
% 1.64/1.17  Cooper               : 0.00
% 1.64/1.17  Total                : 0.40
% 1.64/1.18  Index Insertion      : 0.00
% 1.64/1.18  Index Deletion       : 0.00
% 1.64/1.18  Index Matching       : 0.00
% 1.64/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
