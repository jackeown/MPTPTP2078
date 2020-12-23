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
% DateTime   : Thu Dec  3 09:50:41 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   31 (  38 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  46 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_20,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_62])).

tff(c_108,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_111,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_111])).

tff(c_116,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_35,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | ~ r1_tarski(k1_tarski(A_17),B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    ! [A_17,B_7] : r2_hidden(A_17,k2_xboole_0(k1_tarski(A_17),B_7)) ),
    inference(resolution,[status(thm)],[c_10,c_35])).

tff(c_132,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_44])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:40:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.87/1.18  
% 1.87/1.18  %Foreground sorts:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Background operators:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Foreground operators:
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.18  
% 1.87/1.19  tff(f_50, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 1.87/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.87/1.19  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.87/1.19  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.87/1.19  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.87/1.19  tff(c_20, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.19  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.87/1.19  tff(c_22, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.19  tff(c_62, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.19  tff(c_72, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_62])).
% 1.87/1.19  tff(c_108, plain, (~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_72])).
% 1.87/1.19  tff(c_111, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_8, c_108])).
% 1.87/1.19  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_111])).
% 1.87/1.19  tff(c_116, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_72])).
% 1.87/1.19  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.19  tff(c_35, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | ~r1_tarski(k1_tarski(A_17), B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.87/1.19  tff(c_44, plain, (![A_17, B_7]: (r2_hidden(A_17, k2_xboole_0(k1_tarski(A_17), B_7)))), inference(resolution, [status(thm)], [c_10, c_35])).
% 1.87/1.19  tff(c_132, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_116, c_44])).
% 1.87/1.19  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_132])).
% 1.87/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  Inference rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Ref     : 0
% 1.87/1.19  #Sup     : 24
% 1.87/1.19  #Fact    : 0
% 1.87/1.19  #Define  : 0
% 1.87/1.19  #Split   : 1
% 1.87/1.19  #Chain   : 0
% 1.87/1.19  #Close   : 0
% 1.87/1.19  
% 1.87/1.19  Ordering : KBO
% 1.87/1.19  
% 1.87/1.19  Simplification rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Subsume      : 1
% 1.87/1.19  #Demod        : 7
% 1.87/1.19  #Tautology    : 11
% 1.87/1.19  #SimpNegUnit  : 1
% 1.87/1.19  #BackRed      : 1
% 1.87/1.19  
% 1.87/1.19  #Partial instantiations: 0
% 1.87/1.19  #Strategies tried      : 1
% 1.87/1.19  
% 1.87/1.19  Timing (in seconds)
% 1.87/1.19  ----------------------
% 1.87/1.19  Preprocessing        : 0.29
% 1.87/1.19  Parsing              : 0.15
% 1.87/1.19  CNF conversion       : 0.02
% 1.87/1.19  Main loop            : 0.13
% 1.87/1.19  Inferencing          : 0.04
% 1.87/1.19  Reduction            : 0.04
% 1.87/1.19  Demodulation         : 0.03
% 1.87/1.19  BG Simplification    : 0.01
% 1.87/1.19  Subsumption          : 0.03
% 1.87/1.19  Abstraction          : 0.01
% 1.87/1.19  MUC search           : 0.00
% 1.87/1.19  Cooper               : 0.00
% 1.87/1.19  Total                : 0.44
% 1.87/1.19  Index Insertion      : 0.00
% 1.87/1.19  Index Deletion       : 0.00
% 1.87/1.19  Index Matching       : 0.00
% 1.87/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
