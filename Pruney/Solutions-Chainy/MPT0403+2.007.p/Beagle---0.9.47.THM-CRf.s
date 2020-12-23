%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:41 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  45 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_setfam_1,type,(
    k2_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k2_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k2_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(A,k2_setfam_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_setfam_1)).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_setfam_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    ! [E_65,F_66,A_67,B_68] :
      ( r2_hidden(k2_xboole_0(E_65,F_66),k2_setfam_1(A_67,B_68))
      | ~ r2_hidden(F_66,B_68)
      | ~ r2_hidden(E_65,A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_53,B_54,D_55] :
      ( ~ r1_tarski('#skF_1'(A_53,B_54),D_55)
      | ~ r2_hidden(D_55,B_54)
      | r1_setfam_1(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [A_53,B_54,B_2] :
      ( ~ r2_hidden(k2_xboole_0('#skF_1'(A_53,B_54),B_2),B_54)
      | r1_setfam_1(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_2,c_39])).

tff(c_61,plain,(
    ! [A_75,A_76,B_77,F_78] :
      ( r1_setfam_1(A_75,k2_setfam_1(A_76,B_77))
      | ~ r2_hidden(F_78,B_77)
      | ~ r2_hidden('#skF_1'(A_75,k2_setfam_1(A_76,B_77)),A_76) ) ),
    inference(resolution,[status(thm)],[c_53,c_44])).

tff(c_77,plain,(
    ! [A_79,A_80,A_81,B_82] :
      ( r1_setfam_1(A_79,k2_setfam_1(A_80,A_81))
      | ~ r2_hidden('#skF_1'(A_79,k2_setfam_1(A_80,A_81)),A_80)
      | r1_setfam_1(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_10,c_61])).

tff(c_96,plain,(
    ! [A_83,B_84,A_85] :
      ( r1_setfam_1(A_83,B_84)
      | r1_setfam_1(A_85,k2_setfam_1(A_85,A_83)) ) ),
    inference(resolution,[status(thm)],[c_10,c_77])).

tff(c_36,plain,(
    ~ r1_setfam_1('#skF_9',k2_setfam_1('#skF_9','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_104,plain,(
    ! [B_84] : r1_setfam_1('#skF_9',B_84) ),
    inference(resolution,[status(thm)],[c_96,c_36])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:01:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.13  
% 1.64/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.14  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1
% 1.64/1.14  
% 1.64/1.14  %Foreground sorts:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Background operators:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Foreground operators:
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.14  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.64/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.14  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.64/1.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.64/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.14  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 1.64/1.14  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.64/1.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.64/1.14  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 1.64/1.14  tff('#skF_9', type, '#skF_9': $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.14  tff(k2_setfam_1, type, k2_setfam_1: ($i * $i) > $i).
% 1.64/1.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.64/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.64/1.14  
% 1.64/1.15  tff(f_39, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.64/1.15  tff(f_51, axiom, (![A, B, C]: ((C = k2_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k2_xboole_0(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_setfam_1)).
% 1.64/1.15  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.64/1.15  tff(f_54, negated_conjecture, ~(![A]: r1_setfam_1(A, k2_setfam_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_setfam_1)).
% 1.64/1.15  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_setfam_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.15  tff(c_53, plain, (![E_65, F_66, A_67, B_68]: (r2_hidden(k2_xboole_0(E_65, F_66), k2_setfam_1(A_67, B_68)) | ~r2_hidden(F_66, B_68) | ~r2_hidden(E_65, A_67))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.64/1.15  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.15  tff(c_39, plain, (![A_53, B_54, D_55]: (~r1_tarski('#skF_1'(A_53, B_54), D_55) | ~r2_hidden(D_55, B_54) | r1_setfam_1(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.15  tff(c_44, plain, (![A_53, B_54, B_2]: (~r2_hidden(k2_xboole_0('#skF_1'(A_53, B_54), B_2), B_54) | r1_setfam_1(A_53, B_54))), inference(resolution, [status(thm)], [c_2, c_39])).
% 1.64/1.15  tff(c_61, plain, (![A_75, A_76, B_77, F_78]: (r1_setfam_1(A_75, k2_setfam_1(A_76, B_77)) | ~r2_hidden(F_78, B_77) | ~r2_hidden('#skF_1'(A_75, k2_setfam_1(A_76, B_77)), A_76))), inference(resolution, [status(thm)], [c_53, c_44])).
% 1.64/1.15  tff(c_77, plain, (![A_79, A_80, A_81, B_82]: (r1_setfam_1(A_79, k2_setfam_1(A_80, A_81)) | ~r2_hidden('#skF_1'(A_79, k2_setfam_1(A_80, A_81)), A_80) | r1_setfam_1(A_81, B_82))), inference(resolution, [status(thm)], [c_10, c_61])).
% 1.64/1.15  tff(c_96, plain, (![A_83, B_84, A_85]: (r1_setfam_1(A_83, B_84) | r1_setfam_1(A_85, k2_setfam_1(A_85, A_83)))), inference(resolution, [status(thm)], [c_10, c_77])).
% 1.64/1.15  tff(c_36, plain, (~r1_setfam_1('#skF_9', k2_setfam_1('#skF_9', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.64/1.15  tff(c_104, plain, (![B_84]: (r1_setfam_1('#skF_9', B_84))), inference(resolution, [status(thm)], [c_96, c_36])).
% 1.64/1.15  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_36])).
% 1.64/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.15  
% 1.64/1.15  Inference rules
% 1.64/1.15  ----------------------
% 1.64/1.15  #Ref     : 0
% 1.64/1.15  #Sup     : 11
% 1.64/1.15  #Fact    : 2
% 1.64/1.15  #Define  : 0
% 1.64/1.15  #Split   : 0
% 1.64/1.15  #Chain   : 0
% 1.64/1.15  #Close   : 0
% 1.64/1.15  
% 1.64/1.15  Ordering : KBO
% 1.64/1.15  
% 1.64/1.15  Simplification rules
% 1.64/1.15  ----------------------
% 1.64/1.15  #Subsume      : 0
% 1.64/1.15  #Demod        : 1
% 1.64/1.15  #Tautology    : 0
% 1.64/1.15  #SimpNegUnit  : 0
% 1.64/1.15  #BackRed      : 1
% 1.64/1.15  
% 1.64/1.15  #Partial instantiations: 0
% 1.64/1.15  #Strategies tried      : 1
% 1.64/1.15  
% 1.64/1.15  Timing (in seconds)
% 1.64/1.15  ----------------------
% 1.64/1.15  Preprocessing        : 0.27
% 1.64/1.15  Parsing              : 0.14
% 1.64/1.15  CNF conversion       : 0.03
% 1.64/1.15  Main loop            : 0.11
% 1.64/1.15  Inferencing          : 0.04
% 1.64/1.15  Reduction            : 0.03
% 1.64/1.15  Demodulation         : 0.02
% 1.64/1.15  BG Simplification    : 0.02
% 1.64/1.15  Subsumption          : 0.02
% 1.64/1.15  Abstraction          : 0.01
% 1.64/1.15  MUC search           : 0.00
% 1.64/1.15  Cooper               : 0.00
% 1.64/1.15  Total                : 0.42
% 1.64/1.15  Index Insertion      : 0.00
% 1.64/1.15  Index Deletion       : 0.00
% 1.64/1.15  Index Matching       : 0.00
% 1.64/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
