%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:10 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   43 (  55 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  62 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_48,C_49,B_50] :
      ( ~ r2_hidden(A_48,C_49)
      | ~ r1_xboole_0(k2_tarski(A_48,B_50),C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_65,plain,(
    ! [A_48] : ~ r2_hidden(A_48,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_57])).

tff(c_34,plain,
    ( k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_88,plain,(
    k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_148,plain,(
    ! [C_80,B_81,D_82] :
      ( r2_hidden(k4_tarski(C_80,B_81),k2_zfmisc_1(k1_tarski(C_80),D_82))
      | ~ r2_hidden(B_81,D_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_165,plain,(
    ! [B_81] :
      ( r2_hidden(k4_tarski('#skF_3',B_81),k1_xboole_0)
      | ~ r2_hidden(B_81,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_148])).

tff(c_172,plain,(
    ! [B_83] : ~ r2_hidden(B_83,'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_165])).

tff(c_176,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2,c_172])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_176])).

tff(c_181,plain,(
    k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_192,plain,(
    ! [A_92,D_93,C_94] :
      ( r2_hidden(k4_tarski(A_92,D_93),k2_zfmisc_1(C_94,k1_tarski(D_93)))
      | ~ r2_hidden(A_92,C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_202,plain,(
    ! [A_92] :
      ( r2_hidden(k4_tarski(A_92,'#skF_3'),k1_xboole_0)
      | ~ r2_hidden(A_92,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_192])).

tff(c_207,plain,(
    ! [A_95] : ~ r2_hidden(A_95,'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_202])).

tff(c_211,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2,c_207])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:24:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.18  
% 1.83/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.19  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.83/1.19  
% 1.83/1.19  %Foreground sorts:
% 1.83/1.19  
% 1.83/1.19  
% 1.83/1.19  %Background operators:
% 1.83/1.19  
% 1.83/1.19  
% 1.83/1.19  %Foreground operators:
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.83/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.83/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.83/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.83/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.83/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.83/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.83/1.19  
% 1.83/1.20  tff(f_76, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.83/1.20  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.83/1.20  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.83/1.20  tff(f_66, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.83/1.20  tff(f_55, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 1.83/1.20  tff(f_61, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 1.83/1.20  tff(c_36, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.20  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.83/1.20  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.20  tff(c_57, plain, (![A_48, C_49, B_50]: (~r2_hidden(A_48, C_49) | ~r1_xboole_0(k2_tarski(A_48, B_50), C_49))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.83/1.20  tff(c_65, plain, (![A_48]: (~r2_hidden(A_48, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_57])).
% 1.83/1.20  tff(c_34, plain, (k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.20  tff(c_88, plain, (k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 1.83/1.20  tff(c_148, plain, (![C_80, B_81, D_82]: (r2_hidden(k4_tarski(C_80, B_81), k2_zfmisc_1(k1_tarski(C_80), D_82)) | ~r2_hidden(B_81, D_82))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.20  tff(c_165, plain, (![B_81]: (r2_hidden(k4_tarski('#skF_3', B_81), k1_xboole_0) | ~r2_hidden(B_81, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_148])).
% 1.83/1.20  tff(c_172, plain, (![B_83]: (~r2_hidden(B_83, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_65, c_165])).
% 1.83/1.20  tff(c_176, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2, c_172])).
% 1.83/1.20  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_176])).
% 1.83/1.20  tff(c_181, plain, (k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 1.83/1.20  tff(c_192, plain, (![A_92, D_93, C_94]: (r2_hidden(k4_tarski(A_92, D_93), k2_zfmisc_1(C_94, k1_tarski(D_93))) | ~r2_hidden(A_92, C_94))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.83/1.20  tff(c_202, plain, (![A_92]: (r2_hidden(k4_tarski(A_92, '#skF_3'), k1_xboole_0) | ~r2_hidden(A_92, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_192])).
% 1.83/1.20  tff(c_207, plain, (![A_95]: (~r2_hidden(A_95, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_65, c_202])).
% 1.83/1.20  tff(c_211, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2, c_207])).
% 1.83/1.20  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_211])).
% 1.83/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.20  
% 1.83/1.20  Inference rules
% 1.83/1.20  ----------------------
% 1.83/1.20  #Ref     : 0
% 1.83/1.20  #Sup     : 36
% 1.83/1.20  #Fact    : 0
% 1.83/1.20  #Define  : 0
% 1.83/1.20  #Split   : 1
% 1.83/1.20  #Chain   : 0
% 1.83/1.20  #Close   : 0
% 1.83/1.20  
% 1.83/1.20  Ordering : KBO
% 1.83/1.20  
% 1.83/1.20  Simplification rules
% 1.83/1.20  ----------------------
% 1.83/1.20  #Subsume      : 5
% 1.83/1.20  #Demod        : 0
% 1.83/1.20  #Tautology    : 19
% 1.83/1.20  #SimpNegUnit  : 4
% 1.83/1.20  #BackRed      : 0
% 1.83/1.20  
% 1.83/1.20  #Partial instantiations: 0
% 1.83/1.20  #Strategies tried      : 1
% 1.83/1.20  
% 1.83/1.20  Timing (in seconds)
% 1.83/1.20  ----------------------
% 2.05/1.20  Preprocessing        : 0.30
% 2.05/1.20  Parsing              : 0.17
% 2.05/1.20  CNF conversion       : 0.02
% 2.05/1.20  Main loop            : 0.14
% 2.05/1.20  Inferencing          : 0.05
% 2.05/1.20  Reduction            : 0.04
% 2.05/1.20  Demodulation         : 0.02
% 2.05/1.20  BG Simplification    : 0.01
% 2.05/1.20  Subsumption          : 0.02
% 2.05/1.20  Abstraction          : 0.01
% 2.05/1.20  MUC search           : 0.00
% 2.05/1.20  Cooper               : 0.00
% 2.05/1.20  Total                : 0.47
% 2.05/1.20  Index Insertion      : 0.00
% 2.05/1.20  Index Deletion       : 0.00
% 2.05/1.20  Index Matching       : 0.00
% 2.05/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
