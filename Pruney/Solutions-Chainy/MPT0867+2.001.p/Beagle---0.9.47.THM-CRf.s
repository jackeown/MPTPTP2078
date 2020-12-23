%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:23 EST 2020

% Result     : Theorem 36.76s
% Output     : CNFRefutation 36.76s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  20 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_mcart_1)).

tff(c_4,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_355,plain,(
    ! [A_45,B_46,C_47] : k2_zfmisc_1(k1_tarski(A_45),k2_tarski(B_46,C_47)) = k2_tarski(k4_tarski(A_45,B_46),k4_tarski(A_45,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_10,C_12,B_11] : k2_xboole_0(k2_zfmisc_1(A_10,C_12),k2_zfmisc_1(B_11,C_12)) = k2_zfmisc_1(k2_xboole_0(A_10,B_11),C_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18177,plain,(
    ! [A_296,B_297,C_298,B_299] : k2_xboole_0(k2_tarski(k4_tarski(A_296,B_297),k4_tarski(A_296,C_298)),k2_zfmisc_1(B_299,k2_tarski(B_297,C_298))) = k2_zfmisc_1(k2_xboole_0(k1_tarski(A_296),B_299),k2_tarski(B_297,C_298)) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k2_tarski(C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_376,plain,(
    ! [B_2,C_47,A_1,A_45,B_46] : k2_xboole_0(k2_tarski(A_1,B_2),k2_zfmisc_1(k1_tarski(A_45),k2_tarski(B_46,C_47))) = k2_enumset1(A_1,B_2,k4_tarski(A_45,B_46),k4_tarski(A_45,C_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_2])).

tff(c_18191,plain,(
    ! [A_296,B_297,C_298,A_45] : k2_enumset1(k4_tarski(A_296,B_297),k4_tarski(A_296,C_298),k4_tarski(A_45,B_297),k4_tarski(A_45,C_298)) = k2_zfmisc_1(k2_xboole_0(k1_tarski(A_296),k1_tarski(A_45)),k2_tarski(B_297,C_298)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18177,c_376])).

tff(c_18307,plain,(
    ! [A_296,B_297,C_298,A_45] : k2_enumset1(k4_tarski(A_296,B_297),k4_tarski(A_296,C_298),k4_tarski(A_45,B_297),k4_tarski(A_45,C_298)) = k2_zfmisc_1(k2_tarski(A_296,A_45),k2_tarski(B_297,C_298)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18191])).

tff(c_18,plain,(
    k2_enumset1(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_1','#skF_4'),k4_tarski('#skF_2','#skF_3'),k4_tarski('#skF_2','#skF_4')) != k2_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18307,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:10:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.76/26.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.76/26.25  
% 36.76/26.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.76/26.25  %$ k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 36.76/26.25  
% 36.76/26.25  %Foreground sorts:
% 36.76/26.25  
% 36.76/26.25  
% 36.76/26.25  %Background operators:
% 36.76/26.25  
% 36.76/26.25  
% 36.76/26.25  %Foreground operators:
% 36.76/26.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.76/26.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 36.76/26.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 36.76/26.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 36.76/26.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 36.76/26.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 36.76/26.25  tff('#skF_2', type, '#skF_2': $i).
% 36.76/26.25  tff('#skF_3', type, '#skF_3': $i).
% 36.76/26.25  tff('#skF_1', type, '#skF_1': $i).
% 36.76/26.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.76/26.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 36.76/26.25  tff('#skF_4', type, '#skF_4': $i).
% 36.76/26.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.76/26.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.76/26.25  
% 36.76/26.26  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 36.76/26.26  tff(f_41, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 36.76/26.26  tff(f_37, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 36.76/26.26  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 36.76/26.26  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_mcart_1)).
% 36.76/26.26  tff(c_4, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 36.76/26.26  tff(c_355, plain, (![A_45, B_46, C_47]: (k2_zfmisc_1(k1_tarski(A_45), k2_tarski(B_46, C_47))=k2_tarski(k4_tarski(A_45, B_46), k4_tarski(A_45, C_47)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.76/26.26  tff(c_10, plain, (![A_10, C_12, B_11]: (k2_xboole_0(k2_zfmisc_1(A_10, C_12), k2_zfmisc_1(B_11, C_12))=k2_zfmisc_1(k2_xboole_0(A_10, B_11), C_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 36.76/26.26  tff(c_18177, plain, (![A_296, B_297, C_298, B_299]: (k2_xboole_0(k2_tarski(k4_tarski(A_296, B_297), k4_tarski(A_296, C_298)), k2_zfmisc_1(B_299, k2_tarski(B_297, C_298)))=k2_zfmisc_1(k2_xboole_0(k1_tarski(A_296), B_299), k2_tarski(B_297, C_298)))), inference(superposition, [status(thm), theory('equality')], [c_355, c_10])).
% 36.76/26.26  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.76/26.26  tff(c_376, plain, (![B_2, C_47, A_1, A_45, B_46]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_zfmisc_1(k1_tarski(A_45), k2_tarski(B_46, C_47)))=k2_enumset1(A_1, B_2, k4_tarski(A_45, B_46), k4_tarski(A_45, C_47)))), inference(superposition, [status(thm), theory('equality')], [c_355, c_2])).
% 36.76/26.26  tff(c_18191, plain, (![A_296, B_297, C_298, A_45]: (k2_enumset1(k4_tarski(A_296, B_297), k4_tarski(A_296, C_298), k4_tarski(A_45, B_297), k4_tarski(A_45, C_298))=k2_zfmisc_1(k2_xboole_0(k1_tarski(A_296), k1_tarski(A_45)), k2_tarski(B_297, C_298)))), inference(superposition, [status(thm), theory('equality')], [c_18177, c_376])).
% 36.76/26.26  tff(c_18307, plain, (![A_296, B_297, C_298, A_45]: (k2_enumset1(k4_tarski(A_296, B_297), k4_tarski(A_296, C_298), k4_tarski(A_45, B_297), k4_tarski(A_45, C_298))=k2_zfmisc_1(k2_tarski(A_296, A_45), k2_tarski(B_297, C_298)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18191])).
% 36.76/26.26  tff(c_18, plain, (k2_enumset1(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_1', '#skF_4'), k4_tarski('#skF_2', '#skF_3'), k4_tarski('#skF_2', '#skF_4'))!=k2_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 36.76/26.26  tff(c_66109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18307, c_18])).
% 36.76/26.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.76/26.26  
% 36.76/26.26  Inference rules
% 36.76/26.26  ----------------------
% 36.76/26.26  #Ref     : 0
% 36.76/26.26  #Sup     : 15741
% 36.76/26.26  #Fact    : 0
% 36.76/26.26  #Define  : 0
% 36.76/26.26  #Split   : 0
% 36.76/26.26  #Chain   : 0
% 36.76/26.26  #Close   : 0
% 36.76/26.26  
% 36.76/26.26  Ordering : KBO
% 36.76/26.26  
% 36.76/26.26  Simplification rules
% 36.76/26.26  ----------------------
% 36.76/26.26  #Subsume      : 584
% 36.76/26.26  #Demod        : 25566
% 36.76/26.26  #Tautology    : 4222
% 36.76/26.26  #SimpNegUnit  : 0
% 36.76/26.26  #BackRed      : 3
% 36.76/26.26  
% 36.76/26.26  #Partial instantiations: 0
% 36.76/26.26  #Strategies tried      : 1
% 36.76/26.26  
% 36.76/26.26  Timing (in seconds)
% 36.76/26.26  ----------------------
% 36.76/26.26  Preprocessing        : 0.38
% 36.76/26.26  Parsing              : 0.20
% 36.76/26.26  CNF conversion       : 0.03
% 36.76/26.26  Main loop            : 25.05
% 36.76/26.26  Inferencing          : 3.25
% 36.76/26.26  Reduction            : 18.45
% 36.76/26.26  Demodulation         : 17.76
% 36.76/26.26  BG Simplification    : 0.54
% 36.76/26.26  Subsumption          : 2.33
% 36.76/26.26  Abstraction          : 1.09
% 36.76/26.26  MUC search           : 0.00
% 36.76/26.26  Cooper               : 0.00
% 36.76/26.26  Total                : 25.46
% 36.76/26.26  Index Insertion      : 0.00
% 36.76/26.26  Index Deletion       : 0.00
% 36.76/26.26  Index Matching       : 0.00
% 36.76/26.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
