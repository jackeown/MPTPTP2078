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
% DateTime   : Thu Dec  3 09:54:55 EST 2020

% Result     : Theorem 6.07s
% Output     : CNFRefutation 6.07s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  70 expanded)
%              Number of equality atoms :   25 (  40 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_26,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_130,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_324,plain,(
    ! [A_40,B_41] : k3_xboole_0(k3_xboole_0(A_40,B_41),A_40) = k3_xboole_0(A_40,B_41) ),
    inference(resolution,[status(thm)],[c_12,c_130])).

tff(c_383,plain,(
    ! [A_1,B_41] : k3_xboole_0(A_1,k3_xboole_0(A_1,B_41)) = k3_xboole_0(A_1,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_324])).

tff(c_32,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_154,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_130])).

tff(c_822,plain,(
    ! [A_53,B_54,C_55] : k3_xboole_0(k3_xboole_0(A_53,B_54),C_55) = k3_xboole_0(A_53,k3_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_924,plain,(
    ! [C_55] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_55)) = k3_xboole_0('#skF_1',C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_822])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_153,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_130])).

tff(c_2315,plain,(
    ! [B_86,A_87,B_88] : k3_xboole_0(B_86,k3_xboole_0(A_87,B_88)) = k3_xboole_0(A_87,k3_xboole_0(B_88,B_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_822])).

tff(c_6078,plain,(
    ! [B_108,B_109] : k3_xboole_0(B_108,k3_xboole_0(B_108,B_109)) = k3_xboole_0(B_109,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_2315])).

tff(c_6315,plain,(
    ! [C_55] : k3_xboole_0(k3_xboole_0('#skF_2',C_55),'#skF_1') = k3_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_6078])).

tff(c_7286,plain,(
    ! [C_114] : k3_xboole_0(k3_xboole_0('#skF_2',C_114),'#skF_1') = k3_xboole_0('#skF_1',C_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_6315])).

tff(c_7465,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_7286])).

tff(c_248,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(k1_tarski(A_31),B_32)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_252,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(k1_tarski(A_31),B_32) = k1_tarski(A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_248,c_14])).

tff(c_7559,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7465,c_252])).

tff(c_7629,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7559])).

tff(c_7631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_7629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:53:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.07/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.34  
% 6.07/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.34  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.07/2.34  
% 6.07/2.34  %Foreground sorts:
% 6.07/2.34  
% 6.07/2.34  
% 6.07/2.34  %Background operators:
% 6.07/2.34  
% 6.07/2.34  
% 6.07/2.34  %Foreground operators:
% 6.07/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.07/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.07/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.07/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.07/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.07/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.07/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.07/2.34  tff('#skF_2', type, '#skF_2': $i).
% 6.07/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.07/2.34  tff('#skF_1', type, '#skF_1': $i).
% 6.07/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.07/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.07/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.07/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.07/2.34  
% 6.07/2.35  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 6.07/2.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.07/2.35  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.07/2.35  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.07/2.35  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.07/2.35  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.07/2.35  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.07/2.35  tff(c_26, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.07/2.35  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.07/2.35  tff(c_30, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.07/2.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.07/2.35  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.07/2.35  tff(c_130, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.07/2.35  tff(c_324, plain, (![A_40, B_41]: (k3_xboole_0(k3_xboole_0(A_40, B_41), A_40)=k3_xboole_0(A_40, B_41))), inference(resolution, [status(thm)], [c_12, c_130])).
% 6.07/2.35  tff(c_383, plain, (![A_1, B_41]: (k3_xboole_0(A_1, k3_xboole_0(A_1, B_41))=k3_xboole_0(A_1, B_41))), inference(superposition, [status(thm), theory('equality')], [c_2, c_324])).
% 6.07/2.35  tff(c_32, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.07/2.35  tff(c_154, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_32, c_130])).
% 6.07/2.35  tff(c_822, plain, (![A_53, B_54, C_55]: (k3_xboole_0(k3_xboole_0(A_53, B_54), C_55)=k3_xboole_0(A_53, k3_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.07/2.35  tff(c_924, plain, (![C_55]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_55))=k3_xboole_0('#skF_1', C_55))), inference(superposition, [status(thm), theory('equality')], [c_154, c_822])).
% 6.07/2.35  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.07/2.35  tff(c_153, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_130])).
% 6.07/2.35  tff(c_2315, plain, (![B_86, A_87, B_88]: (k3_xboole_0(B_86, k3_xboole_0(A_87, B_88))=k3_xboole_0(A_87, k3_xboole_0(B_88, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_822])).
% 6.07/2.35  tff(c_6078, plain, (![B_108, B_109]: (k3_xboole_0(B_108, k3_xboole_0(B_108, B_109))=k3_xboole_0(B_109, B_108))), inference(superposition, [status(thm), theory('equality')], [c_153, c_2315])).
% 6.07/2.35  tff(c_6315, plain, (![C_55]: (k3_xboole_0(k3_xboole_0('#skF_2', C_55), '#skF_1')=k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_55)))), inference(superposition, [status(thm), theory('equality')], [c_924, c_6078])).
% 6.07/2.35  tff(c_7286, plain, (![C_114]: (k3_xboole_0(k3_xboole_0('#skF_2', C_114), '#skF_1')=k3_xboole_0('#skF_1', C_114))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_6315])).
% 6.07/2.35  tff(c_7465, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_7286])).
% 6.07/2.35  tff(c_248, plain, (![A_31, B_32]: (r1_tarski(k1_tarski(A_31), B_32) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.07/2.35  tff(c_14, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.07/2.35  tff(c_252, plain, (![A_31, B_32]: (k3_xboole_0(k1_tarski(A_31), B_32)=k1_tarski(A_31) | ~r2_hidden(A_31, B_32))), inference(resolution, [status(thm)], [c_248, c_14])).
% 6.07/2.35  tff(c_7559, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7465, c_252])).
% 6.07/2.35  tff(c_7629, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7559])).
% 6.07/2.35  tff(c_7631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_7629])).
% 6.07/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.35  
% 6.07/2.35  Inference rules
% 6.07/2.35  ----------------------
% 6.07/2.35  #Ref     : 0
% 6.07/2.35  #Sup     : 1848
% 6.07/2.35  #Fact    : 0
% 6.07/2.35  #Define  : 0
% 6.07/2.35  #Split   : 3
% 6.07/2.35  #Chain   : 0
% 6.07/2.35  #Close   : 0
% 6.07/2.35  
% 6.07/2.35  Ordering : KBO
% 6.07/2.35  
% 6.07/2.35  Simplification rules
% 6.07/2.35  ----------------------
% 6.07/2.35  #Subsume      : 74
% 6.07/2.35  #Demod        : 2118
% 6.07/2.35  #Tautology    : 964
% 6.07/2.35  #SimpNegUnit  : 4
% 6.07/2.35  #BackRed      : 2
% 6.07/2.35  
% 6.07/2.35  #Partial instantiations: 0
% 6.07/2.35  #Strategies tried      : 1
% 6.07/2.35  
% 6.07/2.35  Timing (in seconds)
% 6.07/2.35  ----------------------
% 6.07/2.35  Preprocessing        : 0.30
% 6.07/2.35  Parsing              : 0.16
% 6.07/2.35  CNF conversion       : 0.02
% 6.07/2.35  Main loop            : 1.30
% 6.07/2.35  Inferencing          : 0.30
% 6.07/2.35  Reduction            : 0.74
% 6.07/2.35  Demodulation         : 0.64
% 6.07/2.35  BG Simplification    : 0.04
% 6.07/2.35  Subsumption          : 0.17
% 6.07/2.35  Abstraction          : 0.05
% 6.07/2.35  MUC search           : 0.00
% 6.07/2.35  Cooper               : 0.00
% 6.07/2.35  Total                : 1.63
% 6.07/2.35  Index Insertion      : 0.00
% 6.07/2.35  Index Deletion       : 0.00
% 6.07/2.35  Index Matching       : 0.00
% 6.07/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
