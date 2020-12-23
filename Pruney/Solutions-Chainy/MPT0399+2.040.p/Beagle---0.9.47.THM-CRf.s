%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:37 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  58 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k5_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden('#skF_3'(A_45,B_46,C_47),B_46)
      | ~ r2_hidden(C_47,A_45)
      | ~ r1_setfam_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden(A_33,B_34)
      | ~ r2_hidden(A_33,C_35)
      | r2_hidden(A_33,k5_xboole_0(B_34,C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [A_33,A_6] :
      ( r2_hidden(A_33,A_6)
      | ~ r2_hidden(A_33,k1_xboole_0)
      | r2_hidden(A_33,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_71])).

tff(c_143,plain,(
    ! [A_45,C_47,A_6] :
      ( r2_hidden('#skF_3'(A_45,k1_xboole_0,C_47),A_6)
      | ~ r2_hidden(C_47,A_45)
      | ~ r1_setfam_1(A_45,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_127,c_81])).

tff(c_41,plain,(
    ! [A_26,C_27,B_28] :
      ( ~ r2_hidden(A_26,C_27)
      | ~ r2_hidden(A_26,B_28)
      | ~ r2_hidden(A_26,k5_xboole_0(B_28,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_26,A_6] :
      ( ~ r2_hidden(A_26,k1_xboole_0)
      | ~ r2_hidden(A_26,A_6)
      | ~ r2_hidden(A_26,A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_41])).

tff(c_171,plain,(
    ! [A_54,C_55,A_56] :
      ( ~ r2_hidden('#skF_3'(A_54,k1_xboole_0,C_55),A_56)
      | ~ r2_hidden(C_55,A_54)
      | ~ r1_setfam_1(A_54,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_127,c_52])).

tff(c_191,plain,(
    ! [C_57,A_58] :
      ( ~ r2_hidden(C_57,A_58)
      | ~ r1_setfam_1(A_58,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_143,c_171])).

tff(c_212,plain,(
    ! [A_59] :
      ( ~ r1_setfam_1(A_59,k1_xboole_0)
      | k1_xboole_0 = A_59 ) ),
    inference(resolution,[status(thm)],[c_14,c_191])).

tff(c_219,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_212])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n014.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 09:14:07 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.15  %$ r2_hidden > r1_tarski > r1_setfam_1 > k5_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 1.69/1.15  
% 1.69/1.15  %Foreground sorts:
% 1.69/1.15  
% 1.69/1.15  
% 1.69/1.15  %Background operators:
% 1.69/1.15  
% 1.69/1.15  
% 1.69/1.15  %Foreground operators:
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.15  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.69/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.69/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.69/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.69/1.15  
% 1.69/1.16  tff(f_59, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.69/1.16  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.69/1.16  tff(f_54, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.69/1.16  tff(f_42, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.69/1.16  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 1.69/1.16  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.69/1.16  tff(c_28, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.69/1.16  tff(c_14, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.69/1.16  tff(c_127, plain, (![A_45, B_46, C_47]: (r2_hidden('#skF_3'(A_45, B_46, C_47), B_46) | ~r2_hidden(C_47, A_45) | ~r1_setfam_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.69/1.16  tff(c_16, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.69/1.16  tff(c_71, plain, (![A_33, B_34, C_35]: (r2_hidden(A_33, B_34) | ~r2_hidden(A_33, C_35) | r2_hidden(A_33, k5_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.69/1.16  tff(c_81, plain, (![A_33, A_6]: (r2_hidden(A_33, A_6) | ~r2_hidden(A_33, k1_xboole_0) | r2_hidden(A_33, A_6))), inference(superposition, [status(thm), theory('equality')], [c_16, c_71])).
% 1.69/1.16  tff(c_143, plain, (![A_45, C_47, A_6]: (r2_hidden('#skF_3'(A_45, k1_xboole_0, C_47), A_6) | ~r2_hidden(C_47, A_45) | ~r1_setfam_1(A_45, k1_xboole_0))), inference(resolution, [status(thm)], [c_127, c_81])).
% 1.69/1.16  tff(c_41, plain, (![A_26, C_27, B_28]: (~r2_hidden(A_26, C_27) | ~r2_hidden(A_26, B_28) | ~r2_hidden(A_26, k5_xboole_0(B_28, C_27)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.69/1.16  tff(c_52, plain, (![A_26, A_6]: (~r2_hidden(A_26, k1_xboole_0) | ~r2_hidden(A_26, A_6) | ~r2_hidden(A_26, A_6))), inference(superposition, [status(thm), theory('equality')], [c_16, c_41])).
% 1.69/1.16  tff(c_171, plain, (![A_54, C_55, A_56]: (~r2_hidden('#skF_3'(A_54, k1_xboole_0, C_55), A_56) | ~r2_hidden(C_55, A_54) | ~r1_setfam_1(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_127, c_52])).
% 1.69/1.16  tff(c_191, plain, (![C_57, A_58]: (~r2_hidden(C_57, A_58) | ~r1_setfam_1(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_143, c_171])).
% 1.69/1.16  tff(c_212, plain, (![A_59]: (~r1_setfam_1(A_59, k1_xboole_0) | k1_xboole_0=A_59)), inference(resolution, [status(thm)], [c_14, c_191])).
% 1.69/1.16  tff(c_219, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_212])).
% 1.69/1.16  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_219])).
% 1.69/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.16  
% 1.69/1.16  Inference rules
% 1.69/1.16  ----------------------
% 1.69/1.16  #Ref     : 0
% 1.69/1.16  #Sup     : 40
% 1.69/1.16  #Fact    : 0
% 1.69/1.16  #Define  : 0
% 1.69/1.16  #Split   : 0
% 1.69/1.16  #Chain   : 0
% 1.69/1.16  #Close   : 0
% 1.69/1.16  
% 1.69/1.16  Ordering : KBO
% 1.69/1.16  
% 1.69/1.16  Simplification rules
% 1.69/1.16  ----------------------
% 1.69/1.16  #Subsume      : 7
% 1.69/1.16  #Demod        : 2
% 1.69/1.16  #Tautology    : 15
% 1.69/1.16  #SimpNegUnit  : 1
% 1.69/1.16  #BackRed      : 0
% 1.69/1.16  
% 1.69/1.16  #Partial instantiations: 0
% 1.69/1.16  #Strategies tried      : 1
% 1.69/1.16  
% 1.69/1.16  Timing (in seconds)
% 1.69/1.16  ----------------------
% 1.69/1.16  Preprocessing        : 0.27
% 1.69/1.16  Parsing              : 0.14
% 1.69/1.16  CNF conversion       : 0.02
% 1.69/1.16  Main loop            : 0.17
% 1.69/1.16  Inferencing          : 0.07
% 1.69/1.16  Reduction            : 0.04
% 1.69/1.17  Demodulation         : 0.03
% 1.69/1.17  BG Simplification    : 0.01
% 1.69/1.17  Subsumption          : 0.04
% 1.69/1.17  Abstraction          : 0.01
% 1.69/1.17  MUC search           : 0.00
% 1.69/1.17  Cooper               : 0.00
% 1.69/1.17  Total                : 0.47
% 1.69/1.17  Index Insertion      : 0.00
% 1.69/1.17  Index Deletion       : 0.00
% 1.69/1.17  Index Matching       : 0.00
% 1.69/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
