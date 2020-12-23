%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:28 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  48 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(c_48,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_964,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r2_hidden('#skF_2'(A_112,B_113,C_114),B_113)
      | r2_hidden('#skF_3'(A_112,B_113,C_114),C_114)
      | k4_xboole_0(A_112,B_113) = C_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1020,plain,(
    ! [A_118,C_119] :
      ( r2_hidden('#skF_3'(A_118,A_118,C_119),C_119)
      | k4_xboole_0(A_118,A_118) = C_119 ) ),
    inference(resolution,[status(thm)],[c_24,c_964])).

tff(c_32,plain,(
    ! [A_14,C_29] :
      ( r2_hidden('#skF_7'(A_14,k3_tarski(A_14),C_29),A_14)
      | ~ r2_hidden(C_29,k3_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_118,plain,(
    ! [A_60,C_61] :
      ( r2_hidden('#skF_7'(A_60,k3_tarski(A_60),C_61),A_60)
      | ~ r2_hidden(C_61,k3_tarski(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    ! [D_40,B_41,A_42] :
      ( ~ r2_hidden(D_40,B_41)
      | ~ r2_hidden(D_40,k4_xboole_0(A_42,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [D_40,A_13] :
      ( ~ r2_hidden(D_40,A_13)
      | ~ r2_hidden(D_40,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_62])).

tff(c_258,plain,(
    ! [A_75,C_76] :
      ( ~ r2_hidden('#skF_7'(A_75,k3_tarski(A_75),C_76),k1_xboole_0)
      | ~ r2_hidden(C_76,k3_tarski(A_75)) ) ),
    inference(resolution,[status(thm)],[c_118,c_65])).

tff(c_263,plain,(
    ! [C_29] : ~ r2_hidden(C_29,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_32,c_258])).

tff(c_1061,plain,(
    ! [A_120] : k4_xboole_0(A_120,A_120) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1020,c_263])).

tff(c_1078,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1061,c_28])).

tff(c_1091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1078])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.45  
% 2.52/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.46  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.52/1.46  
% 2.52/1.46  %Foreground sorts:
% 2.52/1.46  
% 2.52/1.46  
% 2.52/1.46  %Background operators:
% 2.52/1.46  
% 2.52/1.46  
% 2.52/1.46  %Foreground operators:
% 2.52/1.46  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.52/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.52/1.46  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.52/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.52/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.52/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.52/1.46  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.52/1.46  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.52/1.46  
% 2.96/1.46  tff(f_58, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.96/1.46  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.96/1.46  tff(f_56, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.96/1.46  tff(f_46, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.96/1.46  tff(c_48, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.96/1.46  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.46  tff(c_964, plain, (![A_112, B_113, C_114]: (~r2_hidden('#skF_2'(A_112, B_113, C_114), B_113) | r2_hidden('#skF_3'(A_112, B_113, C_114), C_114) | k4_xboole_0(A_112, B_113)=C_114)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.46  tff(c_1020, plain, (![A_118, C_119]: (r2_hidden('#skF_3'(A_118, A_118, C_119), C_119) | k4_xboole_0(A_118, A_118)=C_119)), inference(resolution, [status(thm)], [c_24, c_964])).
% 2.96/1.46  tff(c_32, plain, (![A_14, C_29]: (r2_hidden('#skF_7'(A_14, k3_tarski(A_14), C_29), A_14) | ~r2_hidden(C_29, k3_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.96/1.46  tff(c_118, plain, (![A_60, C_61]: (r2_hidden('#skF_7'(A_60, k3_tarski(A_60), C_61), A_60) | ~r2_hidden(C_61, k3_tarski(A_60)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.96/1.46  tff(c_28, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.96/1.46  tff(c_62, plain, (![D_40, B_41, A_42]: (~r2_hidden(D_40, B_41) | ~r2_hidden(D_40, k4_xboole_0(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.46  tff(c_65, plain, (![D_40, A_13]: (~r2_hidden(D_40, A_13) | ~r2_hidden(D_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_62])).
% 2.96/1.46  tff(c_258, plain, (![A_75, C_76]: (~r2_hidden('#skF_7'(A_75, k3_tarski(A_75), C_76), k1_xboole_0) | ~r2_hidden(C_76, k3_tarski(A_75)))), inference(resolution, [status(thm)], [c_118, c_65])).
% 2.96/1.46  tff(c_263, plain, (![C_29]: (~r2_hidden(C_29, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_32, c_258])).
% 2.96/1.46  tff(c_1061, plain, (![A_120]: (k4_xboole_0(A_120, A_120)=k3_tarski(k1_xboole_0))), inference(resolution, [status(thm)], [c_1020, c_263])).
% 2.96/1.46  tff(c_1078, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1061, c_28])).
% 2.96/1.46  tff(c_1091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1078])).
% 2.96/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.46  
% 2.96/1.46  Inference rules
% 2.96/1.46  ----------------------
% 2.96/1.46  #Ref     : 0
% 2.96/1.46  #Sup     : 222
% 2.96/1.46  #Fact    : 0
% 2.96/1.46  #Define  : 0
% 2.96/1.46  #Split   : 0
% 2.96/1.46  #Chain   : 0
% 2.96/1.46  #Close   : 0
% 2.96/1.46  
% 2.96/1.47  Ordering : KBO
% 2.96/1.47  
% 2.96/1.47  Simplification rules
% 2.96/1.47  ----------------------
% 2.96/1.47  #Subsume      : 28
% 2.96/1.47  #Demod        : 97
% 2.96/1.47  #Tautology    : 64
% 2.96/1.47  #SimpNegUnit  : 7
% 2.96/1.47  #BackRed      : 14
% 2.96/1.47  
% 2.96/1.47  #Partial instantiations: 0
% 2.96/1.47  #Strategies tried      : 1
% 2.96/1.47  
% 2.96/1.47  Timing (in seconds)
% 2.96/1.47  ----------------------
% 2.96/1.47  Preprocessing        : 0.30
% 2.96/1.47  Parsing              : 0.16
% 2.96/1.47  CNF conversion       : 0.03
% 2.96/1.47  Main loop            : 0.36
% 2.96/1.47  Inferencing          : 0.14
% 2.96/1.47  Reduction            : 0.09
% 2.96/1.47  Demodulation         : 0.06
% 2.96/1.47  BG Simplification    : 0.02
% 2.96/1.47  Subsumption          : 0.08
% 2.96/1.47  Abstraction          : 0.02
% 2.96/1.47  MUC search           : 0.00
% 2.96/1.47  Cooper               : 0.00
% 2.96/1.47  Total                : 0.68
% 2.96/1.47  Index Insertion      : 0.00
% 2.96/1.47  Index Deletion       : 0.00
% 2.96/1.47  Index Matching       : 0.00
% 2.96/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
