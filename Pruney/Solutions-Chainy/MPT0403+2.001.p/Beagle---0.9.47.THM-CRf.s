%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:41 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  47 expanded)
%              Number of equality atoms :    5 (   5 expanded)
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

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k2_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(A,k2_setfam_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_setfam_1)).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_setfam_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [E_69,F_70,A_71,B_72] :
      ( r2_hidden(k2_xboole_0(E_69,F_70),k2_setfam_1(A_71,B_72))
      | ~ r2_hidden(F_70,B_72)
      | ~ r2_hidden(E_69,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    ! [A_73,A_74,B_75] :
      ( r2_hidden(A_73,k2_setfam_1(A_74,B_75))
      | ~ r2_hidden(A_73,B_75)
      | ~ r2_hidden(A_73,A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_85])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    ! [A_57,B_58,D_59] :
      ( ~ r1_tarski('#skF_1'(A_57,B_58),D_59)
      | ~ r2_hidden(D_59,B_58)
      | r1_setfam_1(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden('#skF_1'(A_57,B_58),B_58)
      | r1_setfam_1(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_139,plain,(
    ! [A_108,A_109,B_110] :
      ( r1_setfam_1(A_108,k2_setfam_1(A_109,B_110))
      | ~ r2_hidden('#skF_1'(A_108,k2_setfam_1(A_109,B_110)),B_110)
      | ~ r2_hidden('#skF_1'(A_108,k2_setfam_1(A_109,B_110)),A_109) ) ),
    inference(resolution,[status(thm)],[c_89,c_67])).

tff(c_148,plain,(
    ! [A_111,A_112] :
      ( ~ r2_hidden('#skF_1'(A_111,k2_setfam_1(A_112,A_111)),A_112)
      | r1_setfam_1(A_111,k2_setfam_1(A_112,A_111)) ) ),
    inference(resolution,[status(thm)],[c_16,c_139])).

tff(c_158,plain,(
    ! [A_5] : r1_setfam_1(A_5,k2_setfam_1(A_5,A_5)) ),
    inference(resolution,[status(thm)],[c_16,c_148])).

tff(c_42,plain,(
    ~ r1_setfam_1('#skF_9',k2_setfam_1('#skF_9','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.24  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1
% 1.94/1.24  
% 1.94/1.24  %Foreground sorts:
% 1.94/1.24  
% 1.94/1.24  
% 1.94/1.24  %Background operators:
% 1.94/1.24  
% 1.94/1.24  
% 1.94/1.24  %Foreground operators:
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.24  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.94/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.24  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.94/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.94/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.24  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 1.94/1.24  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.94/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.94/1.24  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 1.94/1.24  tff('#skF_9', type, '#skF_9': $i).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.24  tff(k2_setfam_1, type, k2_setfam_1: ($i * $i) > $i).
% 1.94/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.24  
% 1.94/1.25  tff(f_45, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.94/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.94/1.25  tff(f_57, axiom, (![A, B, C]: ((C = k2_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k2_xboole_0(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_setfam_1)).
% 1.94/1.25  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.94/1.25  tff(f_60, negated_conjecture, ~(![A]: r1_setfam_1(A, k2_setfam_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_setfam_1)).
% 1.94/1.25  tff(c_16, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_setfam_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.25  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.25  tff(c_85, plain, (![E_69, F_70, A_71, B_72]: (r2_hidden(k2_xboole_0(E_69, F_70), k2_setfam_1(A_71, B_72)) | ~r2_hidden(F_70, B_72) | ~r2_hidden(E_69, A_71))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.25  tff(c_89, plain, (![A_73, A_74, B_75]: (r2_hidden(A_73, k2_setfam_1(A_74, B_75)) | ~r2_hidden(A_73, B_75) | ~r2_hidden(A_73, A_74))), inference(superposition, [status(thm), theory('equality')], [c_2, c_85])).
% 1.94/1.25  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.25  tff(c_62, plain, (![A_57, B_58, D_59]: (~r1_tarski('#skF_1'(A_57, B_58), D_59) | ~r2_hidden(D_59, B_58) | r1_setfam_1(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.25  tff(c_67, plain, (![A_57, B_58]: (~r2_hidden('#skF_1'(A_57, B_58), B_58) | r1_setfam_1(A_57, B_58))), inference(resolution, [status(thm)], [c_8, c_62])).
% 1.94/1.25  tff(c_139, plain, (![A_108, A_109, B_110]: (r1_setfam_1(A_108, k2_setfam_1(A_109, B_110)) | ~r2_hidden('#skF_1'(A_108, k2_setfam_1(A_109, B_110)), B_110) | ~r2_hidden('#skF_1'(A_108, k2_setfam_1(A_109, B_110)), A_109))), inference(resolution, [status(thm)], [c_89, c_67])).
% 1.94/1.25  tff(c_148, plain, (![A_111, A_112]: (~r2_hidden('#skF_1'(A_111, k2_setfam_1(A_112, A_111)), A_112) | r1_setfam_1(A_111, k2_setfam_1(A_112, A_111)))), inference(resolution, [status(thm)], [c_16, c_139])).
% 1.94/1.25  tff(c_158, plain, (![A_5]: (r1_setfam_1(A_5, k2_setfam_1(A_5, A_5)))), inference(resolution, [status(thm)], [c_16, c_148])).
% 1.94/1.25  tff(c_42, plain, (~r1_setfam_1('#skF_9', k2_setfam_1('#skF_9', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.94/1.25  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_42])).
% 1.94/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.25  
% 1.94/1.25  Inference rules
% 1.94/1.25  ----------------------
% 1.94/1.25  #Ref     : 0
% 1.94/1.25  #Sup     : 21
% 1.94/1.25  #Fact    : 0
% 1.94/1.25  #Define  : 0
% 1.94/1.25  #Split   : 0
% 1.94/1.25  #Chain   : 0
% 1.94/1.25  #Close   : 0
% 1.94/1.25  
% 1.94/1.25  Ordering : KBO
% 1.94/1.25  
% 1.94/1.25  Simplification rules
% 1.94/1.25  ----------------------
% 1.94/1.25  #Subsume      : 0
% 1.94/1.25  #Demod        : 3
% 1.94/1.25  #Tautology    : 7
% 1.94/1.25  #SimpNegUnit  : 0
% 1.94/1.25  #BackRed      : 1
% 1.94/1.25  
% 1.94/1.25  #Partial instantiations: 0
% 1.94/1.25  #Strategies tried      : 1
% 1.94/1.25  
% 1.94/1.25  Timing (in seconds)
% 1.94/1.25  ----------------------
% 1.94/1.25  Preprocessing        : 0.28
% 1.94/1.25  Parsing              : 0.15
% 1.94/1.25  CNF conversion       : 0.03
% 1.94/1.25  Main loop            : 0.17
% 1.94/1.25  Inferencing          : 0.07
% 1.94/1.25  Reduction            : 0.04
% 1.94/1.25  Demodulation         : 0.03
% 1.94/1.25  BG Simplification    : 0.02
% 1.94/1.25  Subsumption          : 0.04
% 1.94/1.25  Abstraction          : 0.01
% 1.94/1.25  MUC search           : 0.00
% 1.94/1.25  Cooper               : 0.00
% 1.94/1.25  Total                : 0.48
% 1.94/1.25  Index Insertion      : 0.00
% 1.94/1.25  Index Deletion       : 0.00
% 1.94/1.25  Index Matching       : 0.00
% 1.94/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
