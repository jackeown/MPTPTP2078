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
% DateTime   : Thu Dec  3 09:57:42 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  40 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k3_xboole_0 > k3_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k3_setfam_1,type,(
    k3_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k3_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k3_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(k3_setfam_1(A,A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_setfam_1)).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_setfam_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_17,B_18,D_44] :
      ( r2_hidden('#skF_7'(A_17,B_18,k3_setfam_1(A_17,B_18),D_44),A_17)
      | ~ r2_hidden(D_44,k3_setfam_1(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_130,plain,(
    ! [A_98,B_99,D_100] :
      ( k3_xboole_0('#skF_7'(A_98,B_99,k3_setfam_1(A_98,B_99),D_100),'#skF_8'(A_98,B_99,k3_setfam_1(A_98,B_99),D_100)) = D_100
      | ~ r2_hidden(D_100,k3_setfam_1(A_98,B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_151,plain,(
    ! [D_101,A_102,B_103] :
      ( r1_tarski(D_101,'#skF_7'(A_102,B_103,k3_setfam_1(A_102,B_103),D_101))
      | ~ r2_hidden(D_101,k3_setfam_1(A_102,B_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_4])).

tff(c_10,plain,(
    ! [A_5,B_6,D_14] :
      ( ~ r1_tarski('#skF_1'(A_5,B_6),D_14)
      | ~ r2_hidden(D_14,B_6)
      | r1_setfam_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_163,plain,(
    ! [A_107,B_108,A_109,B_110] :
      ( ~ r2_hidden('#skF_7'(A_107,B_108,k3_setfam_1(A_107,B_108),'#skF_1'(A_109,B_110)),B_110)
      | r1_setfam_1(A_109,B_110)
      | ~ r2_hidden('#skF_1'(A_109,B_110),k3_setfam_1(A_107,B_108)) ) ),
    inference(resolution,[status(thm)],[c_151,c_10])).

tff(c_169,plain,(
    ! [A_111,A_112,B_113] :
      ( r1_setfam_1(A_111,A_112)
      | ~ r2_hidden('#skF_1'(A_111,A_112),k3_setfam_1(A_112,B_113)) ) ),
    inference(resolution,[status(thm)],[c_20,c_163])).

tff(c_174,plain,(
    ! [B_6,B_113] : r1_setfam_1(k3_setfam_1(B_6,B_113),B_6) ),
    inference(resolution,[status(thm)],[c_12,c_169])).

tff(c_38,plain,(
    ~ r1_setfam_1(k3_setfam_1('#skF_9','#skF_9'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:43:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.24  
% 2.00/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.24  %$ r2_hidden > r1_tarski > r1_setfam_1 > k3_xboole_0 > k3_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1
% 2.00/1.24  
% 2.00/1.24  %Foreground sorts:
% 2.00/1.24  
% 2.00/1.24  
% 2.00/1.24  %Background operators:
% 2.00/1.24  
% 2.00/1.24  
% 2.00/1.24  %Foreground operators:
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.24  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.00/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.24  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.00/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.00/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.24  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.00/1.24  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.00/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.00/1.24  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.00/1.24  tff('#skF_9', type, '#skF_9': $i).
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.00/1.24  tff(k3_setfam_1, type, k3_setfam_1: ($i * $i) > $i).
% 2.00/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.24  
% 2.05/1.25  tff(f_41, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.05/1.25  tff(f_53, axiom, (![A, B, C]: ((C = k3_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k3_xboole_0(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_setfam_1)).
% 2.05/1.25  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.05/1.25  tff(f_56, negated_conjecture, ~(![A]: r1_setfam_1(k3_setfam_1(A, A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_setfam_1)).
% 2.05/1.25  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_setfam_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.25  tff(c_20, plain, (![A_17, B_18, D_44]: (r2_hidden('#skF_7'(A_17, B_18, k3_setfam_1(A_17, B_18), D_44), A_17) | ~r2_hidden(D_44, k3_setfam_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.05/1.25  tff(c_130, plain, (![A_98, B_99, D_100]: (k3_xboole_0('#skF_7'(A_98, B_99, k3_setfam_1(A_98, B_99), D_100), '#skF_8'(A_98, B_99, k3_setfam_1(A_98, B_99), D_100))=D_100 | ~r2_hidden(D_100, k3_setfam_1(A_98, B_99)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.05/1.25  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.25  tff(c_151, plain, (![D_101, A_102, B_103]: (r1_tarski(D_101, '#skF_7'(A_102, B_103, k3_setfam_1(A_102, B_103), D_101)) | ~r2_hidden(D_101, k3_setfam_1(A_102, B_103)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_4])).
% 2.05/1.25  tff(c_10, plain, (![A_5, B_6, D_14]: (~r1_tarski('#skF_1'(A_5, B_6), D_14) | ~r2_hidden(D_14, B_6) | r1_setfam_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.25  tff(c_163, plain, (![A_107, B_108, A_109, B_110]: (~r2_hidden('#skF_7'(A_107, B_108, k3_setfam_1(A_107, B_108), '#skF_1'(A_109, B_110)), B_110) | r1_setfam_1(A_109, B_110) | ~r2_hidden('#skF_1'(A_109, B_110), k3_setfam_1(A_107, B_108)))), inference(resolution, [status(thm)], [c_151, c_10])).
% 2.05/1.25  tff(c_169, plain, (![A_111, A_112, B_113]: (r1_setfam_1(A_111, A_112) | ~r2_hidden('#skF_1'(A_111, A_112), k3_setfam_1(A_112, B_113)))), inference(resolution, [status(thm)], [c_20, c_163])).
% 2.05/1.25  tff(c_174, plain, (![B_6, B_113]: (r1_setfam_1(k3_setfam_1(B_6, B_113), B_6))), inference(resolution, [status(thm)], [c_12, c_169])).
% 2.05/1.25  tff(c_38, plain, (~r1_setfam_1(k3_setfam_1('#skF_9', '#skF_9'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.05/1.25  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_38])).
% 2.05/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.25  
% 2.05/1.25  Inference rules
% 2.05/1.25  ----------------------
% 2.05/1.25  #Ref     : 0
% 2.05/1.25  #Sup     : 29
% 2.05/1.25  #Fact    : 0
% 2.05/1.25  #Define  : 0
% 2.05/1.25  #Split   : 0
% 2.05/1.25  #Chain   : 0
% 2.05/1.25  #Close   : 0
% 2.05/1.25  
% 2.05/1.25  Ordering : KBO
% 2.05/1.25  
% 2.05/1.25  Simplification rules
% 2.05/1.25  ----------------------
% 2.05/1.25  #Subsume      : 3
% 2.05/1.25  #Demod        : 6
% 2.05/1.25  #Tautology    : 14
% 2.05/1.25  #SimpNegUnit  : 0
% 2.05/1.25  #BackRed      : 1
% 2.05/1.25  
% 2.05/1.25  #Partial instantiations: 0
% 2.05/1.25  #Strategies tried      : 1
% 2.05/1.25  
% 2.05/1.25  Timing (in seconds)
% 2.05/1.25  ----------------------
% 2.05/1.25  Preprocessing        : 0.27
% 2.05/1.25  Parsing              : 0.14
% 2.05/1.25  CNF conversion       : 0.03
% 2.05/1.25  Main loop            : 0.17
% 2.05/1.25  Inferencing          : 0.06
% 2.05/1.25  Reduction            : 0.05
% 2.05/1.25  Demodulation         : 0.04
% 2.05/1.25  BG Simplification    : 0.02
% 2.05/1.25  Subsumption          : 0.03
% 2.05/1.25  Abstraction          : 0.01
% 2.05/1.25  MUC search           : 0.00
% 2.05/1.25  Cooper               : 0.00
% 2.05/1.25  Total                : 0.47
% 2.05/1.25  Index Insertion      : 0.00
% 2.05/1.25  Index Deletion       : 0.00
% 2.05/1.26  Index Matching       : 0.00
% 2.05/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
