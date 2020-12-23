%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:41 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  54 expanded)
%              Number of equality atoms :    6 (   7 expanded)
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

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k2_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k2_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(A,k2_setfam_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_setfam_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(A_52,B_53) = B_53
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_94,plain,(
    ! [E_71,F_72,A_73,B_74] :
      ( r2_hidden(k2_xboole_0(E_71,F_72),k2_setfam_1(A_73,B_74))
      | ~ r2_hidden(F_72,B_74)
      | ~ r2_hidden(E_71,A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_98,plain,(
    ! [B_75,A_76,B_77] :
      ( r2_hidden(B_75,k2_setfam_1(A_76,B_77))
      | ~ r2_hidden(B_75,B_77)
      | ~ r2_hidden(B_75,A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_94])).

tff(c_67,plain,(
    ! [A_59,B_60,D_61] :
      ( ~ r1_tarski('#skF_1'(A_59,B_60),D_61)
      | ~ r2_hidden(D_61,B_60)
      | r1_setfam_1(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,(
    ! [A_59,B_60] :
      ( ~ r2_hidden('#skF_1'(A_59,B_60),B_60)
      | r1_setfam_1(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_160,plain,(
    ! [A_113,A_114,B_115] :
      ( r1_setfam_1(A_113,k2_setfam_1(A_114,B_115))
      | ~ r2_hidden('#skF_1'(A_113,k2_setfam_1(A_114,B_115)),B_115)
      | ~ r2_hidden('#skF_1'(A_113,k2_setfam_1(A_114,B_115)),A_114) ) ),
    inference(resolution,[status(thm)],[c_98,c_72])).

tff(c_174,plain,(
    ! [A_121,A_122] :
      ( ~ r2_hidden('#skF_1'(A_121,k2_setfam_1(A_122,A_121)),A_122)
      | r1_setfam_1(A_121,k2_setfam_1(A_122,A_121)) ) ),
    inference(resolution,[status(thm)],[c_16,c_160])).

tff(c_184,plain,(
    ! [A_5] : r1_setfam_1(A_5,k2_setfam_1(A_5,A_5)) ),
    inference(resolution,[status(thm)],[c_16,c_174])).

tff(c_42,plain,(
    ~ r1_setfam_1('#skF_9',k2_setfam_1('#skF_9','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.25  
% 1.97/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.25  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1
% 2.10/1.25  
% 2.10/1.25  %Foreground sorts:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Background operators:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Foreground operators:
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.25  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.10/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.25  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.10/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.10/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.25  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.10/1.25  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.10/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.25  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.10/1.25  tff('#skF_9', type, '#skF_9': $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.25  tff(k2_setfam_1, type, k2_setfam_1: ($i * $i) > $i).
% 2.10/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.25  
% 2.10/1.26  tff(f_47, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.10/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.10/1.26  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.10/1.26  tff(f_59, axiom, (![A, B, C]: ((C = k2_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k2_xboole_0(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_setfam_1)).
% 2.10/1.26  tff(f_62, negated_conjecture, ~(![A]: r1_setfam_1(A, k2_setfam_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_setfam_1)).
% 2.10/1.26  tff(c_16, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_setfam_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.26  tff(c_45, plain, (![A_52, B_53]: (k2_xboole_0(A_52, B_53)=B_53 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.26  tff(c_49, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_45])).
% 2.10/1.26  tff(c_94, plain, (![E_71, F_72, A_73, B_74]: (r2_hidden(k2_xboole_0(E_71, F_72), k2_setfam_1(A_73, B_74)) | ~r2_hidden(F_72, B_74) | ~r2_hidden(E_71, A_73))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.26  tff(c_98, plain, (![B_75, A_76, B_77]: (r2_hidden(B_75, k2_setfam_1(A_76, B_77)) | ~r2_hidden(B_75, B_77) | ~r2_hidden(B_75, A_76))), inference(superposition, [status(thm), theory('equality')], [c_49, c_94])).
% 2.10/1.26  tff(c_67, plain, (![A_59, B_60, D_61]: (~r1_tarski('#skF_1'(A_59, B_60), D_61) | ~r2_hidden(D_61, B_60) | r1_setfam_1(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.26  tff(c_72, plain, (![A_59, B_60]: (~r2_hidden('#skF_1'(A_59, B_60), B_60) | r1_setfam_1(A_59, B_60))), inference(resolution, [status(thm)], [c_6, c_67])).
% 2.10/1.26  tff(c_160, plain, (![A_113, A_114, B_115]: (r1_setfam_1(A_113, k2_setfam_1(A_114, B_115)) | ~r2_hidden('#skF_1'(A_113, k2_setfam_1(A_114, B_115)), B_115) | ~r2_hidden('#skF_1'(A_113, k2_setfam_1(A_114, B_115)), A_114))), inference(resolution, [status(thm)], [c_98, c_72])).
% 2.10/1.26  tff(c_174, plain, (![A_121, A_122]: (~r2_hidden('#skF_1'(A_121, k2_setfam_1(A_122, A_121)), A_122) | r1_setfam_1(A_121, k2_setfam_1(A_122, A_121)))), inference(resolution, [status(thm)], [c_16, c_160])).
% 2.10/1.26  tff(c_184, plain, (![A_5]: (r1_setfam_1(A_5, k2_setfam_1(A_5, A_5)))), inference(resolution, [status(thm)], [c_16, c_174])).
% 2.10/1.26  tff(c_42, plain, (~r1_setfam_1('#skF_9', k2_setfam_1('#skF_9', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.10/1.26  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_42])).
% 2.10/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  Inference rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Ref     : 0
% 2.10/1.26  #Sup     : 27
% 2.10/1.26  #Fact    : 0
% 2.10/1.26  #Define  : 0
% 2.10/1.26  #Split   : 0
% 2.10/1.26  #Chain   : 0
% 2.10/1.26  #Close   : 0
% 2.10/1.26  
% 2.10/1.26  Ordering : KBO
% 2.10/1.26  
% 2.10/1.26  Simplification rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Subsume      : 0
% 2.10/1.26  #Demod        : 3
% 2.10/1.26  #Tautology    : 9
% 2.10/1.26  #SimpNegUnit  : 0
% 2.10/1.26  #BackRed      : 1
% 2.10/1.26  
% 2.10/1.26  #Partial instantiations: 0
% 2.10/1.26  #Strategies tried      : 1
% 2.10/1.26  
% 2.10/1.26  Timing (in seconds)
% 2.10/1.26  ----------------------
% 2.10/1.26  Preprocessing        : 0.28
% 2.10/1.26  Parsing              : 0.14
% 2.10/1.26  CNF conversion       : 0.02
% 2.10/1.26  Main loop            : 0.19
% 2.10/1.26  Inferencing          : 0.08
% 2.10/1.26  Reduction            : 0.04
% 2.10/1.26  Demodulation         : 0.03
% 2.10/1.26  BG Simplification    : 0.02
% 2.10/1.26  Subsumption          : 0.04
% 2.10/1.26  Abstraction          : 0.01
% 2.10/1.26  MUC search           : 0.00
% 2.10/1.26  Cooper               : 0.00
% 2.10/1.26  Total                : 0.49
% 2.10/1.26  Index Insertion      : 0.00
% 2.10/1.26  Index Deletion       : 0.00
% 2.10/1.26  Index Matching       : 0.00
% 2.10/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
