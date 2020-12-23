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
% DateTime   : Thu Dec  3 09:50:39 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  69 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_54,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_445,plain,(
    ! [A_129,B_130] : k5_xboole_0(k5_xboole_0(A_129,B_130),k3_xboole_0(A_129,B_130)) = k2_xboole_0(A_129,B_130) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1128,plain,(
    ! [A_163,B_164] : k5_xboole_0(k5_xboole_0(A_163,B_164),k3_xboole_0(B_164,A_163)) = k2_xboole_0(A_163,B_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_445])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_472,plain,(
    ! [A_3,B_4] : k5_xboole_0(k5_xboole_0(A_3,B_4),k3_xboole_0(B_4,A_3)) = k2_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_445])).

tff(c_1140,plain,(
    ! [B_164,A_163] : k2_xboole_0(B_164,A_163) = k2_xboole_0(A_163,B_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_1128,c_472])).

tff(c_56,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_250,plain,(
    ! [A_97,B_98] :
      ( r2_xboole_0(A_97,B_98)
      | B_98 = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( ~ r2_xboole_0(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_357,plain,(
    ! [B_117,A_118] :
      ( ~ r1_tarski(B_117,A_118)
      | B_117 = A_118
      | ~ r1_tarski(A_118,B_117) ) ),
    inference(resolution,[status(thm)],[c_250,c_14])).

tff(c_384,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_357])).

tff(c_417,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_1249,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_417])).

tff(c_1253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1249])).

tff(c_1254,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_22,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_209,plain,(
    ! [B_86,C_87,A_88] :
      ( r2_hidden(B_86,C_87)
      | ~ r1_tarski(k2_tarski(A_88,B_86),C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_237,plain,(
    ! [B_92,A_93,B_94] : r2_hidden(B_92,k2_xboole_0(k2_tarski(A_93,B_92),B_94)) ),
    inference(resolution,[status(thm)],[c_16,c_209])).

tff(c_244,plain,(
    ! [A_19,B_94] : r2_hidden(A_19,k2_xboole_0(k1_tarski(A_19),B_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_237])).

tff(c_1260,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1254,c_244])).

tff(c_1270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.30  % Computer   : n006.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % DateTime   : Tue Dec  1 20:51:52 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.49  
% 3.54/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.49  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.54/1.49  
% 3.54/1.49  %Foreground sorts:
% 3.54/1.49  
% 3.54/1.49  
% 3.54/1.49  %Background operators:
% 3.54/1.49  
% 3.54/1.49  
% 3.54/1.49  %Foreground operators:
% 3.54/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.54/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.54/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.54/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.54/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.54/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.54/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.49  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.54/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.54/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.54/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.54/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.49  
% 3.54/1.51  tff(f_93, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.54/1.51  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.54/1.51  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.54/1.51  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.54/1.51  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.54/1.51  tff(f_36, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.54/1.51  tff(f_45, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 3.54/1.51  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.54/1.51  tff(f_88, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.54/1.51  tff(c_54, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.54/1.51  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.54/1.51  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.51  tff(c_445, plain, (![A_129, B_130]: (k5_xboole_0(k5_xboole_0(A_129, B_130), k3_xboole_0(A_129, B_130))=k2_xboole_0(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.54/1.51  tff(c_1128, plain, (![A_163, B_164]: (k5_xboole_0(k5_xboole_0(A_163, B_164), k3_xboole_0(B_164, A_163))=k2_xboole_0(A_163, B_164))), inference(superposition, [status(thm), theory('equality')], [c_2, c_445])).
% 3.54/1.51  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.54/1.51  tff(c_472, plain, (![A_3, B_4]: (k5_xboole_0(k5_xboole_0(A_3, B_4), k3_xboole_0(B_4, A_3))=k2_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_445])).
% 3.54/1.51  tff(c_1140, plain, (![B_164, A_163]: (k2_xboole_0(B_164, A_163)=k2_xboole_0(A_163, B_164))), inference(superposition, [status(thm), theory('equality')], [c_1128, c_472])).
% 3.54/1.51  tff(c_56, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.54/1.51  tff(c_250, plain, (![A_97, B_98]: (r2_xboole_0(A_97, B_98) | B_98=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.54/1.51  tff(c_14, plain, (![B_11, A_10]: (~r2_xboole_0(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.54/1.51  tff(c_357, plain, (![B_117, A_118]: (~r1_tarski(B_117, A_118) | B_117=A_118 | ~r1_tarski(A_118, B_117))), inference(resolution, [status(thm)], [c_250, c_14])).
% 3.54/1.51  tff(c_384, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_357])).
% 3.54/1.51  tff(c_417, plain, (~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_384])).
% 3.54/1.51  tff(c_1249, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1140, c_417])).
% 3.54/1.51  tff(c_1253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_1249])).
% 3.54/1.51  tff(c_1254, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_384])).
% 3.54/1.51  tff(c_22, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.54/1.51  tff(c_209, plain, (![B_86, C_87, A_88]: (r2_hidden(B_86, C_87) | ~r1_tarski(k2_tarski(A_88, B_86), C_87))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.54/1.51  tff(c_237, plain, (![B_92, A_93, B_94]: (r2_hidden(B_92, k2_xboole_0(k2_tarski(A_93, B_92), B_94)))), inference(resolution, [status(thm)], [c_16, c_209])).
% 3.54/1.51  tff(c_244, plain, (![A_19, B_94]: (r2_hidden(A_19, k2_xboole_0(k1_tarski(A_19), B_94)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_237])).
% 3.54/1.51  tff(c_1260, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1254, c_244])).
% 3.54/1.51  tff(c_1270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1260])).
% 3.54/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.51  
% 3.54/1.51  Inference rules
% 3.54/1.51  ----------------------
% 3.54/1.51  #Ref     : 0
% 3.54/1.51  #Sup     : 308
% 3.54/1.51  #Fact    : 0
% 3.54/1.51  #Define  : 0
% 3.54/1.51  #Split   : 1
% 3.54/1.51  #Chain   : 0
% 3.54/1.51  #Close   : 0
% 3.54/1.51  
% 3.54/1.51  Ordering : KBO
% 3.54/1.51  
% 3.54/1.51  Simplification rules
% 3.54/1.51  ----------------------
% 3.54/1.51  #Subsume      : 14
% 3.54/1.51  #Demod        : 108
% 3.54/1.51  #Tautology    : 96
% 3.54/1.51  #SimpNegUnit  : 1
% 3.54/1.51  #BackRed      : 3
% 3.54/1.51  
% 3.54/1.51  #Partial instantiations: 0
% 3.54/1.51  #Strategies tried      : 1
% 3.54/1.51  
% 3.54/1.51  Timing (in seconds)
% 3.54/1.51  ----------------------
% 3.69/1.51  Preprocessing        : 0.33
% 3.69/1.51  Parsing              : 0.18
% 3.69/1.51  CNF conversion       : 0.02
% 3.69/1.51  Main loop            : 0.51
% 3.69/1.51  Inferencing          : 0.16
% 3.69/1.51  Reduction            : 0.22
% 3.69/1.51  Demodulation         : 0.18
% 3.69/1.51  BG Simplification    : 0.03
% 3.69/1.51  Subsumption          : 0.07
% 3.69/1.51  Abstraction          : 0.03
% 3.69/1.51  MUC search           : 0.00
% 3.69/1.51  Cooper               : 0.00
% 3.69/1.51  Total                : 0.87
% 3.69/1.51  Index Insertion      : 0.00
% 3.69/1.51  Index Deletion       : 0.00
% 3.69/1.51  Index Matching       : 0.00
% 3.69/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
