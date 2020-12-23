%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:50 EST 2020

% Result     : Theorem 34.20s
% Output     : CNFRefutation 34.20s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.20/24.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.20/24.71  
% 34.20/24.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.20/24.71  %$ k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 34.20/24.71  
% 34.20/24.71  %Foreground sorts:
% 34.20/24.71  
% 34.20/24.71  
% 34.20/24.71  %Background operators:
% 34.20/24.71  
% 34.20/24.71  
% 34.20/24.71  %Foreground operators:
% 34.20/24.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.20/24.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 34.20/24.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 34.20/24.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 34.20/24.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 34.20/24.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 34.20/24.71  tff('#skF_2', type, '#skF_2': $i).
% 34.20/24.71  tff('#skF_3', type, '#skF_3': $i).
% 34.20/24.71  tff('#skF_1', type, '#skF_1': $i).
% 34.20/24.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.20/24.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 34.20/24.71  tff('#skF_4', type, '#skF_4': $i).
% 34.20/24.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.20/24.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 34.20/24.71  
% 34.20/24.72  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 34.20/24.72  tff(f_41, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 34.20/24.72  tff(f_37, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 34.20/24.72  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 34.20/24.72  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 34.20/24.72  tff(c_4, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 34.20/24.72  tff(c_355, plain, (![A_45, B_46, C_47]: (k2_zfmisc_1(k1_tarski(A_45), k2_tarski(B_46, C_47))=k2_tarski(k4_tarski(A_45, B_46), k4_tarski(A_45, C_47)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 34.20/24.72  tff(c_10, plain, (![A_10, C_12, B_11]: (k2_xboole_0(k2_zfmisc_1(A_10, C_12), k2_zfmisc_1(B_11, C_12))=k2_zfmisc_1(k2_xboole_0(A_10, B_11), C_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 34.20/24.72  tff(c_18177, plain, (![A_296, B_297, C_298, B_299]: (k2_xboole_0(k2_tarski(k4_tarski(A_296, B_297), k4_tarski(A_296, C_298)), k2_zfmisc_1(B_299, k2_tarski(B_297, C_298)))=k2_zfmisc_1(k2_xboole_0(k1_tarski(A_296), B_299), k2_tarski(B_297, C_298)))), inference(superposition, [status(thm), theory('equality')], [c_355, c_10])).
% 34.20/24.72  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 34.20/24.72  tff(c_376, plain, (![B_2, C_47, A_1, A_45, B_46]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_zfmisc_1(k1_tarski(A_45), k2_tarski(B_46, C_47)))=k2_enumset1(A_1, B_2, k4_tarski(A_45, B_46), k4_tarski(A_45, C_47)))), inference(superposition, [status(thm), theory('equality')], [c_355, c_2])).
% 34.20/24.72  tff(c_18191, plain, (![A_296, B_297, C_298, A_45]: (k2_enumset1(k4_tarski(A_296, B_297), k4_tarski(A_296, C_298), k4_tarski(A_45, B_297), k4_tarski(A_45, C_298))=k2_zfmisc_1(k2_xboole_0(k1_tarski(A_296), k1_tarski(A_45)), k2_tarski(B_297, C_298)))), inference(superposition, [status(thm), theory('equality')], [c_18177, c_376])).
% 34.20/24.72  tff(c_18307, plain, (![A_296, B_297, C_298, A_45]: (k2_enumset1(k4_tarski(A_296, B_297), k4_tarski(A_296, C_298), k4_tarski(A_45, B_297), k4_tarski(A_45, C_298))=k2_zfmisc_1(k2_tarski(A_296, A_45), k2_tarski(B_297, C_298)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18191])).
% 34.20/24.72  tff(c_18, plain, (k2_enumset1(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_1', '#skF_4'), k4_tarski('#skF_2', '#skF_3'), k4_tarski('#skF_2', '#skF_4'))!=k2_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 34.20/24.72  tff(c_66109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18307, c_18])).
% 34.20/24.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.20/24.72  
% 34.20/24.72  Inference rules
% 34.20/24.72  ----------------------
% 34.20/24.72  #Ref     : 0
% 34.20/24.72  #Sup     : 15741
% 34.20/24.72  #Fact    : 0
% 34.20/24.72  #Define  : 0
% 34.20/24.72  #Split   : 0
% 34.20/24.72  #Chain   : 0
% 34.20/24.72  #Close   : 0
% 34.20/24.72  
% 34.20/24.72  Ordering : KBO
% 34.20/24.72  
% 34.20/24.72  Simplification rules
% 34.20/24.72  ----------------------
% 34.20/24.72  #Subsume      : 584
% 34.20/24.72  #Demod        : 25566
% 34.20/24.72  #Tautology    : 4222
% 34.20/24.72  #SimpNegUnit  : 0
% 34.20/24.72  #BackRed      : 3
% 34.20/24.72  
% 34.20/24.72  #Partial instantiations: 0
% 34.20/24.72  #Strategies tried      : 1
% 34.20/24.72  
% 34.20/24.72  Timing (in seconds)
% 34.20/24.72  ----------------------
% 34.20/24.72  Preprocessing        : 0.30
% 34.20/24.72  Parsing              : 0.16
% 34.20/24.72  CNF conversion       : 0.01
% 34.20/24.72  Main loop            : 23.60
% 34.20/24.72  Inferencing          : 2.90
% 34.20/24.72  Reduction            : 17.54
% 34.20/24.72  Demodulation         : 16.91
% 34.20/24.72  BG Simplification    : 0.49
% 34.20/24.72  Subsumption          : 2.21
% 34.20/24.72  Abstraction          : 0.99
% 34.20/24.72  MUC search           : 0.00
% 34.20/24.73  Cooper               : 0.00
% 34.20/24.73  Total                : 23.91
% 34.20/24.73  Index Insertion      : 0.00
% 34.20/24.73  Index Deletion       : 0.00
% 34.20/24.73  Index Matching       : 0.00
% 34.20/24.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
