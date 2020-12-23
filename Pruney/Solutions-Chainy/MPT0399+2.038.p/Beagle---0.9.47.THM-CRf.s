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
% DateTime   : Thu Dec  3 09:57:36 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  63 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_761,plain,(
    ! [A_111,B_112,C_113] :
      ( r2_hidden('#skF_4'(A_111,B_112,C_113),B_112)
      | ~ r2_hidden(C_113,A_111)
      | ~ r1_setfam_1(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_74,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_10,C_40] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_40,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_74])).

tff(c_94,plain,(
    ! [C_40] : ~ r2_hidden(C_40,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_776,plain,(
    ! [C_114,A_115] :
      ( ~ r2_hidden(C_114,A_115)
      | ~ r1_setfam_1(A_115,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_761,c_94])).

tff(c_793,plain,(
    ! [A_116] :
      ( ~ r1_setfam_1(A_116,k1_xboole_0)
      | k1_xboole_0 = A_116 ) ),
    inference(resolution,[status(thm)],[c_6,c_776])).

tff(c_808,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34,c_793])).

tff(c_816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_808])).

tff(c_817,plain,(
    ! [A_10] : ~ r1_xboole_0(A_10,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_819,plain,(
    ! [A_118,C_119,B_120] :
      ( r1_xboole_0(A_118,k4_xboole_0(C_119,B_120))
      | ~ r1_tarski(A_118,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_825,plain,(
    ! [A_118,A_14] :
      ( r1_xboole_0(A_118,k1_xboole_0)
      | ~ r1_tarski(A_118,A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_819])).

tff(c_826,plain,(
    ! [A_118,A_14] : ~ r1_tarski(A_118,A_14) ),
    inference(negUnitSimplification,[status(thm)],[c_817,c_825])).

tff(c_30,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k3_tarski(A_30),k3_tarski(B_31))
      | ~ r1_setfam_1(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_827,plain,(
    ! [A_30,B_31] : ~ r1_setfam_1(A_30,B_31) ),
    inference(negUnitSimplification,[status(thm)],[c_826,c_30])).

tff(c_830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_827,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.39  
% 2.60/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1
% 2.60/1.39  
% 2.60/1.39  %Foreground sorts:
% 2.60/1.39  
% 2.60/1.39  
% 2.60/1.39  %Background operators:
% 2.60/1.39  
% 2.60/1.39  
% 2.60/1.39  %Foreground operators:
% 2.60/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.39  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.60/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.60/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.60/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.60/1.39  
% 2.60/1.40  tff(f_85, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.60/1.40  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.60/1.40  tff(f_76, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.60/1.40  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.60/1.40  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.60/1.40  tff(f_59, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.60/1.40  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.60/1.40  tff(f_80, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.60/1.40  tff(c_32, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.60/1.40  tff(c_34, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.60/1.40  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.60/1.40  tff(c_761, plain, (![A_111, B_112, C_113]: (r2_hidden('#skF_4'(A_111, B_112, C_113), B_112) | ~r2_hidden(C_113, A_111) | ~r1_setfam_1(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.60/1.40  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.60/1.40  tff(c_74, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.40  tff(c_81, plain, (![A_10, C_40]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_74])).
% 2.60/1.40  tff(c_94, plain, (![C_40]: (~r2_hidden(C_40, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_81])).
% 2.60/1.40  tff(c_776, plain, (![C_114, A_115]: (~r2_hidden(C_114, A_115) | ~r1_setfam_1(A_115, k1_xboole_0))), inference(resolution, [status(thm)], [c_761, c_94])).
% 2.60/1.40  tff(c_793, plain, (![A_116]: (~r1_setfam_1(A_116, k1_xboole_0) | k1_xboole_0=A_116)), inference(resolution, [status(thm)], [c_6, c_776])).
% 2.60/1.40  tff(c_808, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_34, c_793])).
% 2.60/1.40  tff(c_816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_808])).
% 2.60/1.40  tff(c_817, plain, (![A_10]: (~r1_xboole_0(A_10, k1_xboole_0))), inference(splitRight, [status(thm)], [c_81])).
% 2.60/1.40  tff(c_16, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.60/1.40  tff(c_819, plain, (![A_118, C_119, B_120]: (r1_xboole_0(A_118, k4_xboole_0(C_119, B_120)) | ~r1_tarski(A_118, B_120))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.60/1.40  tff(c_825, plain, (![A_118, A_14]: (r1_xboole_0(A_118, k1_xboole_0) | ~r1_tarski(A_118, A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_819])).
% 2.60/1.40  tff(c_826, plain, (![A_118, A_14]: (~r1_tarski(A_118, A_14))), inference(negUnitSimplification, [status(thm)], [c_817, c_825])).
% 2.60/1.40  tff(c_30, plain, (![A_30, B_31]: (r1_tarski(k3_tarski(A_30), k3_tarski(B_31)) | ~r1_setfam_1(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.40  tff(c_827, plain, (![A_30, B_31]: (~r1_setfam_1(A_30, B_31))), inference(negUnitSimplification, [status(thm)], [c_826, c_30])).
% 2.60/1.40  tff(c_830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_827, c_34])).
% 2.60/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.40  
% 2.60/1.40  Inference rules
% 2.60/1.40  ----------------------
% 2.60/1.40  #Ref     : 0
% 2.60/1.40  #Sup     : 181
% 2.60/1.40  #Fact    : 0
% 2.60/1.40  #Define  : 0
% 2.60/1.40  #Split   : 3
% 2.60/1.40  #Chain   : 0
% 2.60/1.40  #Close   : 0
% 2.60/1.40  
% 2.60/1.40  Ordering : KBO
% 2.60/1.40  
% 2.60/1.40  Simplification rules
% 2.60/1.40  ----------------------
% 2.60/1.40  #Subsume      : 17
% 2.60/1.40  #Demod        : 68
% 2.60/1.40  #Tautology    : 98
% 2.60/1.40  #SimpNegUnit  : 7
% 2.60/1.40  #BackRed      : 5
% 2.60/1.40  
% 2.60/1.40  #Partial instantiations: 0
% 2.60/1.40  #Strategies tried      : 1
% 2.60/1.40  
% 2.60/1.40  Timing (in seconds)
% 2.60/1.40  ----------------------
% 2.60/1.41  Preprocessing        : 0.28
% 2.60/1.41  Parsing              : 0.15
% 2.60/1.41  CNF conversion       : 0.02
% 2.60/1.41  Main loop            : 0.29
% 2.60/1.41  Inferencing          : 0.11
% 2.60/1.41  Reduction            : 0.08
% 2.60/1.41  Demodulation         : 0.06
% 2.60/1.41  BG Simplification    : 0.01
% 2.60/1.41  Subsumption          : 0.05
% 2.60/1.41  Abstraction          : 0.01
% 2.60/1.41  MUC search           : 0.00
% 2.60/1.41  Cooper               : 0.00
% 2.60/1.41  Total                : 0.59
% 2.60/1.41  Index Insertion      : 0.00
% 2.60/1.41  Index Deletion       : 0.00
% 2.60/1.41  Index Matching       : 0.00
% 2.60/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
