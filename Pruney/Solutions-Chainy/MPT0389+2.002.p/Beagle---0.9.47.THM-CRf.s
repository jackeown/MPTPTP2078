%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:12 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  50 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    ! [A_21,B_22] :
      ( r2_hidden('#skF_2'(A_21,B_22),A_21)
      | r1_tarski(B_22,k1_setfam_1(A_21))
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [A_30,B_31,B_32] :
      ( r2_hidden('#skF_2'(A_30,B_31),B_32)
      | ~ r1_tarski(A_30,B_32)
      | r1_tarski(B_31,k1_setfam_1(A_30))
      | k1_xboole_0 = A_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_setfam_1(B_7),A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_40,plain,(
    ! [B_23,A_24] :
      ( ~ r1_tarski(B_23,'#skF_2'(A_24,B_23))
      | r1_tarski(B_23,k1_setfam_1(A_24))
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    ! [B_7,A_24] :
      ( r1_tarski(k1_setfam_1(B_7),k1_setfam_1(A_24))
      | k1_xboole_0 = A_24
      | ~ r2_hidden('#skF_2'(A_24,k1_setfam_1(B_7)),B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_40])).

tff(c_70,plain,(
    ! [A_33,B_34] :
      ( ~ r1_tarski(A_33,B_34)
      | r1_tarski(k1_setfam_1(B_34),k1_setfam_1(A_33))
      | k1_xboole_0 = A_33 ) ),
    inference(resolution,[status(thm)],[c_61,c_44])).

tff(c_14,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_73,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_70,c_14])).

tff(c_76,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_73])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n015.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 15:01:08 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.18  
% 1.74/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.18  %$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.74/1.18  
% 1.74/1.18  %Foreground sorts:
% 1.74/1.18  
% 1.74/1.18  
% 1.74/1.18  %Background operators:
% 1.74/1.18  
% 1.74/1.18  
% 1.74/1.18  %Foreground operators:
% 1.74/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.74/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.74/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.74/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.74/1.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.74/1.18  
% 1.81/1.19  tff(f_52, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 1.81/1.19  tff(f_45, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 1.81/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.81/1.19  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.81/1.19  tff(c_16, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.19  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.19  tff(c_36, plain, (![A_21, B_22]: (r2_hidden('#skF_2'(A_21, B_22), A_21) | r1_tarski(B_22, k1_setfam_1(A_21)) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.81/1.19  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.19  tff(c_61, plain, (![A_30, B_31, B_32]: (r2_hidden('#skF_2'(A_30, B_31), B_32) | ~r1_tarski(A_30, B_32) | r1_tarski(B_31, k1_setfam_1(A_30)) | k1_xboole_0=A_30)), inference(resolution, [status(thm)], [c_36, c_2])).
% 1.81/1.19  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k1_setfam_1(B_7), A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.81/1.19  tff(c_40, plain, (![B_23, A_24]: (~r1_tarski(B_23, '#skF_2'(A_24, B_23)) | r1_tarski(B_23, k1_setfam_1(A_24)) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.81/1.19  tff(c_44, plain, (![B_7, A_24]: (r1_tarski(k1_setfam_1(B_7), k1_setfam_1(A_24)) | k1_xboole_0=A_24 | ~r2_hidden('#skF_2'(A_24, k1_setfam_1(B_7)), B_7))), inference(resolution, [status(thm)], [c_8, c_40])).
% 1.81/1.19  tff(c_70, plain, (![A_33, B_34]: (~r1_tarski(A_33, B_34) | r1_tarski(k1_setfam_1(B_34), k1_setfam_1(A_33)) | k1_xboole_0=A_33)), inference(resolution, [status(thm)], [c_61, c_44])).
% 1.81/1.19  tff(c_14, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.19  tff(c_73, plain, (~r1_tarski('#skF_3', '#skF_4') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_70, c_14])).
% 1.81/1.19  tff(c_76, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_73])).
% 1.81/1.19  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_76])).
% 1.81/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  Inference rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Ref     : 0
% 1.81/1.19  #Sup     : 11
% 1.81/1.19  #Fact    : 0
% 1.81/1.19  #Define  : 0
% 1.81/1.19  #Split   : 0
% 1.81/1.19  #Chain   : 0
% 1.81/1.19  #Close   : 0
% 1.81/1.19  
% 1.81/1.19  Ordering : KBO
% 1.81/1.19  
% 1.81/1.19  Simplification rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Subsume      : 0
% 1.81/1.19  #Demod        : 2
% 1.81/1.19  #Tautology    : 2
% 1.81/1.19  #SimpNegUnit  : 1
% 1.81/1.19  #BackRed      : 0
% 1.81/1.19  
% 1.81/1.19  #Partial instantiations: 0
% 1.81/1.19  #Strategies tried      : 1
% 1.81/1.19  
% 1.81/1.19  Timing (in seconds)
% 1.81/1.19  ----------------------
% 1.81/1.19  Preprocessing        : 0.29
% 1.81/1.19  Parsing              : 0.16
% 1.81/1.19  CNF conversion       : 0.02
% 1.81/1.19  Main loop            : 0.11
% 1.81/1.19  Inferencing          : 0.05
% 1.81/1.19  Reduction            : 0.03
% 1.81/1.19  Demodulation         : 0.02
% 1.81/1.19  BG Simplification    : 0.01
% 1.81/1.19  Subsumption          : 0.02
% 1.81/1.19  Abstraction          : 0.01
% 1.81/1.19  MUC search           : 0.00
% 1.81/1.19  Cooper               : 0.00
% 1.81/1.19  Total                : 0.43
% 1.81/1.19  Index Insertion      : 0.00
% 1.81/1.19  Index Deletion       : 0.00
% 1.81/1.19  Index Matching       : 0.00
% 1.81/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
