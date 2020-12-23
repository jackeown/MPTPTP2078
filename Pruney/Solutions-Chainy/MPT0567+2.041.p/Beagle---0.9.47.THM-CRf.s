%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:20 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  54 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_26,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),B_28)
      | r2_hidden('#skF_2'(A_27,B_28),A_27)
      | B_28 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_37,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_xboole_0(A_19,B_20)
      | ~ r2_hidden(C_21,k3_xboole_0(A_19,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,(
    ! [A_9,C_21] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r2_hidden(C_21,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_37])).

tff(c_42,plain,(
    ! [C_21] : ~ r2_hidden(C_21,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_40])).

tff(c_76,plain,(
    ! [B_28] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_28),B_28)
      | k1_xboole_0 = B_28 ) ),
    inference(resolution,[status(thm)],[c_54,c_42])).

tff(c_119,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden('#skF_4'(A_36,B_37,C_38),B_37)
      | ~ r2_hidden(A_36,k10_relat_1(C_38,B_37))
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_130,plain,(
    ! [A_39,C_40] :
      ( ~ r2_hidden(A_39,k10_relat_1(C_40,k1_xboole_0))
      | ~ v1_relat_1(C_40) ) ),
    inference(resolution,[status(thm)],[c_119,c_42])).

tff(c_157,plain,(
    ! [C_44] :
      ( ~ v1_relat_1(C_44)
      | k10_relat_1(C_44,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_76,c_130])).

tff(c_160,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_157])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:43:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.20  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 1.88/1.20  
% 1.88/1.20  %Foreground sorts:
% 1.88/1.20  
% 1.88/1.20  
% 1.88/1.20  %Background operators:
% 1.88/1.20  
% 1.88/1.20  
% 1.88/1.20  %Foreground operators:
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.88/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.88/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.88/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.88/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.88/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.20  
% 1.88/1.21  tff(f_66, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 1.88/1.21  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 1.88/1.21  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.88/1.21  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.88/1.21  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.88/1.21  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.88/1.21  tff(c_26, plain, (k10_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.88/1.21  tff(c_28, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.88/1.21  tff(c_54, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), B_28) | r2_hidden('#skF_2'(A_27, B_28), A_27) | B_28=A_27)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.21  tff(c_16, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.21  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.21  tff(c_37, plain, (![A_19, B_20, C_21]: (~r1_xboole_0(A_19, B_20) | ~r2_hidden(C_21, k3_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.88/1.21  tff(c_40, plain, (![A_9, C_21]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r2_hidden(C_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_37])).
% 1.88/1.21  tff(c_42, plain, (![C_21]: (~r2_hidden(C_21, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_40])).
% 1.88/1.21  tff(c_76, plain, (![B_28]: (r2_hidden('#skF_1'(k1_xboole_0, B_28), B_28) | k1_xboole_0=B_28)), inference(resolution, [status(thm)], [c_54, c_42])).
% 1.88/1.21  tff(c_119, plain, (![A_36, B_37, C_38]: (r2_hidden('#skF_4'(A_36, B_37, C_38), B_37) | ~r2_hidden(A_36, k10_relat_1(C_38, B_37)) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.88/1.21  tff(c_130, plain, (![A_39, C_40]: (~r2_hidden(A_39, k10_relat_1(C_40, k1_xboole_0)) | ~v1_relat_1(C_40))), inference(resolution, [status(thm)], [c_119, c_42])).
% 1.88/1.21  tff(c_157, plain, (![C_44]: (~v1_relat_1(C_44) | k10_relat_1(C_44, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_76, c_130])).
% 1.88/1.21  tff(c_160, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_157])).
% 1.88/1.21  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_160])).
% 1.88/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  Inference rules
% 1.88/1.21  ----------------------
% 1.88/1.21  #Ref     : 0
% 1.88/1.21  #Sup     : 24
% 1.88/1.21  #Fact    : 0
% 1.88/1.21  #Define  : 0
% 1.88/1.21  #Split   : 0
% 1.88/1.21  #Chain   : 0
% 1.88/1.21  #Close   : 0
% 1.88/1.21  
% 1.88/1.21  Ordering : KBO
% 1.88/1.21  
% 1.88/1.21  Simplification rules
% 1.88/1.21  ----------------------
% 1.88/1.21  #Subsume      : 4
% 1.88/1.21  #Demod        : 3
% 1.88/1.21  #Tautology    : 8
% 1.88/1.21  #SimpNegUnit  : 1
% 1.88/1.21  #BackRed      : 0
% 1.88/1.21  
% 1.88/1.21  #Partial instantiations: 0
% 1.88/1.21  #Strategies tried      : 1
% 1.88/1.21  
% 1.88/1.21  Timing (in seconds)
% 1.88/1.21  ----------------------
% 1.88/1.21  Preprocessing        : 0.28
% 1.88/1.21  Parsing              : 0.16
% 1.88/1.21  CNF conversion       : 0.02
% 1.88/1.21  Main loop            : 0.15
% 1.88/1.21  Inferencing          : 0.07
% 1.88/1.21  Reduction            : 0.04
% 1.88/1.21  Demodulation         : 0.03
% 1.88/1.21  BG Simplification    : 0.01
% 1.88/1.21  Subsumption          : 0.02
% 1.88/1.21  Abstraction          : 0.01
% 1.88/1.21  MUC search           : 0.00
% 1.88/1.21  Cooper               : 0.00
% 1.88/1.21  Total                : 0.46
% 1.88/1.21  Index Insertion      : 0.00
% 1.88/1.21  Index Deletion       : 0.00
% 1.88/1.21  Index Matching       : 0.00
% 1.88/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
