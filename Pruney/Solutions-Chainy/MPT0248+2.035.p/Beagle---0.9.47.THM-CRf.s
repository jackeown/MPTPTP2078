%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:08 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   52 (  82 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 178 expanded)
%              Number of equality atoms :   43 ( 158 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_33,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_52,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_691,plain,(
    ! [B_48,A_49] :
      ( k1_tarski(B_48) = A_49
      | k1_xboole_0 = A_49
      | ~ r1_tarski(A_49,k1_tarski(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_701,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48,c_691])).

tff(c_712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_52,c_701])).

tff(c_713,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_714,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_740,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_714,c_28])).

tff(c_741,plain,(
    ! [B_50,A_51] : k2_xboole_0(B_50,A_51) = k2_xboole_0(A_51,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_716,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_30])).

tff(c_756,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_716])).

tff(c_795,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_8])).

tff(c_1451,plain,(
    ! [B_77,A_78] :
      ( k1_tarski(B_77) = A_78
      | k1_xboole_0 = A_78
      | ~ r1_tarski(A_78,k1_tarski(B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1458,plain,(
    ! [A_78] :
      ( k1_tarski('#skF_1') = A_78
      | k1_xboole_0 = A_78
      | ~ r1_tarski(A_78,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_1451])).

tff(c_1468,plain,(
    ! [A_79] :
      ( A_79 = '#skF_2'
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_1458])).

tff(c_1475,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_795,c_1468])).

tff(c_1487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_740,c_1475])).

tff(c_1488,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1489,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1490,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1489,c_6])).

tff(c_1596,plain,(
    ! [A_89,B_90] :
      ( k2_xboole_0(A_89,B_90) = B_90
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1616,plain,(
    ! [A_5] : k2_xboole_0('#skF_2',A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_1490,c_1596])).

tff(c_1617,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_30])).

tff(c_1619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1488,c_1617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:40:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.52  
% 2.91/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.53  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.91/1.53  
% 2.91/1.53  %Foreground sorts:
% 2.91/1.53  
% 2.91/1.53  
% 2.91/1.53  %Background operators:
% 2.91/1.53  
% 2.91/1.53  
% 2.91/1.53  %Foreground operators:
% 2.91/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.91/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.91/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.91/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.91/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.91/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.53  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.91/1.53  
% 2.91/1.54  tff(f_68, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.91/1.54  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.91/1.54  tff(f_49, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.91/1.54  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.91/1.54  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.91/1.54  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.91/1.54  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.91/1.54  tff(c_33, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 2.91/1.54  tff(c_24, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.91/1.54  tff(c_52, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.91/1.54  tff(c_30, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.91/1.54  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.54  tff(c_48, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_8])).
% 2.91/1.54  tff(c_691, plain, (![B_48, A_49]: (k1_tarski(B_48)=A_49 | k1_xboole_0=A_49 | ~r1_tarski(A_49, k1_tarski(B_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.91/1.54  tff(c_701, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_48, c_691])).
% 2.91/1.54  tff(c_712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_52, c_701])).
% 2.91/1.54  tff(c_713, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.91/1.54  tff(c_714, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.91/1.54  tff(c_28, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.91/1.54  tff(c_740, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_714, c_714, c_28])).
% 2.91/1.54  tff(c_741, plain, (![B_50, A_51]: (k2_xboole_0(B_50, A_51)=k2_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.91/1.54  tff(c_716, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_714, c_30])).
% 2.91/1.54  tff(c_756, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_741, c_716])).
% 2.91/1.54  tff(c_795, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_756, c_8])).
% 2.91/1.54  tff(c_1451, plain, (![B_77, A_78]: (k1_tarski(B_77)=A_78 | k1_xboole_0=A_78 | ~r1_tarski(A_78, k1_tarski(B_77)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.91/1.54  tff(c_1458, plain, (![A_78]: (k1_tarski('#skF_1')=A_78 | k1_xboole_0=A_78 | ~r1_tarski(A_78, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_714, c_1451])).
% 2.91/1.54  tff(c_1468, plain, (![A_79]: (A_79='#skF_2' | k1_xboole_0=A_79 | ~r1_tarski(A_79, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_714, c_1458])).
% 2.91/1.54  tff(c_1475, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_795, c_1468])).
% 2.91/1.54  tff(c_1487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_713, c_740, c_1475])).
% 2.91/1.54  tff(c_1488, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.91/1.54  tff(c_1489, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.91/1.54  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.91/1.54  tff(c_1490, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1489, c_6])).
% 2.91/1.54  tff(c_1596, plain, (![A_89, B_90]: (k2_xboole_0(A_89, B_90)=B_90 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.54  tff(c_1616, plain, (![A_5]: (k2_xboole_0('#skF_2', A_5)=A_5)), inference(resolution, [status(thm)], [c_1490, c_1596])).
% 2.91/1.54  tff(c_1617, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_30])).
% 2.91/1.54  tff(c_1619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1488, c_1617])).
% 2.91/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.54  
% 2.91/1.54  Inference rules
% 2.91/1.54  ----------------------
% 2.91/1.54  #Ref     : 0
% 2.91/1.54  #Sup     : 382
% 2.91/1.54  #Fact    : 0
% 2.91/1.54  #Define  : 0
% 2.91/1.54  #Split   : 4
% 2.91/1.54  #Chain   : 0
% 2.91/1.54  #Close   : 0
% 2.91/1.54  
% 2.91/1.54  Ordering : KBO
% 2.91/1.54  
% 2.91/1.54  Simplification rules
% 2.91/1.54  ----------------------
% 2.91/1.54  #Subsume      : 11
% 2.91/1.54  #Demod        : 377
% 2.91/1.54  #Tautology    : 322
% 2.91/1.54  #SimpNegUnit  : 4
% 2.91/1.54  #BackRed      : 4
% 2.91/1.54  
% 2.91/1.54  #Partial instantiations: 0
% 2.91/1.54  #Strategies tried      : 1
% 2.91/1.54  
% 2.91/1.54  Timing (in seconds)
% 2.91/1.54  ----------------------
% 2.91/1.54  Preprocessing        : 0.31
% 2.91/1.54  Parsing              : 0.16
% 2.91/1.54  CNF conversion       : 0.02
% 2.91/1.54  Main loop            : 0.41
% 2.91/1.54  Inferencing          : 0.13
% 2.91/1.54  Reduction            : 0.18
% 2.91/1.54  Demodulation         : 0.15
% 2.91/1.54  BG Simplification    : 0.02
% 2.91/1.54  Subsumption          : 0.05
% 2.91/1.54  Abstraction          : 0.02
% 2.91/1.54  MUC search           : 0.00
% 2.91/1.54  Cooper               : 0.00
% 2.91/1.54  Total                : 0.75
% 2.91/1.54  Index Insertion      : 0.00
% 2.91/1.54  Index Deletion       : 0.00
% 2.91/1.54  Index Matching       : 0.00
% 2.91/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
