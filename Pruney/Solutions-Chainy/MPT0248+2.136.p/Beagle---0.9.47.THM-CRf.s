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
% DateTime   : Thu Dec  3 09:50:23 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   60 (  99 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 205 expanded)
%              Number of equality atoms :   45 ( 166 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_63,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_41,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_235,plain,(
    ! [B_42,A_43] :
      ( k1_tarski(B_42) = A_43
      | k1_xboole_0 = A_43
      | ~ r1_tarski(A_43,k1_tarski(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_245,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_49,c_235])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_41,c_245])).

tff(c_257,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_6,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_45,plain,(
    ! [A_6] : r1_tarski(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_42])).

tff(c_258,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_259,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_2') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_6])).

tff(c_361,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,k2_xboole_0(C_56,B_57))
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_383,plain,(
    ! [A_59,A_60] :
      ( r1_tarski(A_59,A_60)
      | ~ r1_tarski(A_59,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_361])).

tff(c_389,plain,(
    ! [A_61] : r1_tarski('#skF_2',A_61) ),
    inference(resolution,[status(thm)],[c_45,c_383])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_398,plain,(
    ! [A_61] : k2_xboole_0('#skF_2',A_61) = A_61 ),
    inference(resolution,[status(thm)],[c_389,c_4])).

tff(c_400,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_30])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_400])).

tff(c_403,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_404,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_449,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_404,c_28])).

tff(c_428,plain,(
    ! [A_63,B_64] : r1_tarski(A_63,k2_xboole_0(A_63,B_64)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_434,plain,(
    ! [A_6] : r1_tarski(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_428])).

tff(c_411,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_30])).

tff(c_607,plain,(
    ! [A_78,C_79,B_80] :
      ( r1_tarski(A_78,k2_xboole_0(C_79,B_80))
      | ~ r1_tarski(A_78,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_627,plain,(
    ! [A_81] :
      ( r1_tarski(A_81,'#skF_2')
      | ~ r1_tarski(A_81,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_607])).

tff(c_687,plain,(
    ! [A_86] :
      ( k2_xboole_0(A_86,'#skF_2') = '#skF_2'
      | ~ r1_tarski(A_86,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_627,c_4])).

tff(c_698,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_434,c_687])).

tff(c_714,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_8])).

tff(c_777,plain,(
    ! [B_92,A_93] :
      ( k1_tarski(B_92) = A_93
      | k1_xboole_0 = A_93
      | ~ r1_tarski(A_93,k1_tarski(B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_788,plain,(
    ! [A_93] :
      ( k1_tarski('#skF_1') = A_93
      | k1_xboole_0 = A_93
      | ~ r1_tarski(A_93,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_777])).

tff(c_794,plain,(
    ! [A_94] :
      ( A_94 = '#skF_2'
      | k1_xboole_0 = A_94
      | ~ r1_tarski(A_94,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_788])).

tff(c_797,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_714,c_794])).

tff(c_812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_449,c_797])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.31  
% 2.13/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.31  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.31  
% 2.13/1.31  %Foreground sorts:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Background operators:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Foreground operators:
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.31  
% 2.13/1.32  tff(f_70, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.13/1.32  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.13/1.32  tff(f_49, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.13/1.32  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.13/1.32  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.13/1.32  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.13/1.32  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.32  tff(c_63, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 2.13/1.32  tff(c_24, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.32  tff(c_41, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.13/1.32  tff(c_30, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.32  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.32  tff(c_49, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_8])).
% 2.13/1.32  tff(c_235, plain, (![B_42, A_43]: (k1_tarski(B_42)=A_43 | k1_xboole_0=A_43 | ~r1_tarski(A_43, k1_tarski(B_42)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.32  tff(c_245, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_49, c_235])).
% 2.13/1.32  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_41, c_245])).
% 2.13/1.32  tff(c_257, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.13/1.32  tff(c_6, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.32  tff(c_42, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.32  tff(c_45, plain, (![A_6]: (r1_tarski(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_42])).
% 2.13/1.32  tff(c_258, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.13/1.32  tff(c_259, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_2')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_258, c_6])).
% 2.13/1.32  tff(c_361, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, k2_xboole_0(C_56, B_57)) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.32  tff(c_383, plain, (![A_59, A_60]: (r1_tarski(A_59, A_60) | ~r1_tarski(A_59, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_259, c_361])).
% 2.13/1.32  tff(c_389, plain, (![A_61]: (r1_tarski('#skF_2', A_61))), inference(resolution, [status(thm)], [c_45, c_383])).
% 2.13/1.32  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.32  tff(c_398, plain, (![A_61]: (k2_xboole_0('#skF_2', A_61)=A_61)), inference(resolution, [status(thm)], [c_389, c_4])).
% 2.13/1.32  tff(c_400, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_398, c_30])).
% 2.13/1.32  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257, c_400])).
% 2.13/1.32  tff(c_403, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.13/1.32  tff(c_404, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.13/1.32  tff(c_28, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.32  tff(c_449, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_404, c_404, c_28])).
% 2.13/1.32  tff(c_428, plain, (![A_63, B_64]: (r1_tarski(A_63, k2_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.32  tff(c_434, plain, (![A_6]: (r1_tarski(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_428])).
% 2.13/1.32  tff(c_411, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_404, c_30])).
% 2.13/1.32  tff(c_607, plain, (![A_78, C_79, B_80]: (r1_tarski(A_78, k2_xboole_0(C_79, B_80)) | ~r1_tarski(A_78, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.32  tff(c_627, plain, (![A_81]: (r1_tarski(A_81, '#skF_2') | ~r1_tarski(A_81, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_411, c_607])).
% 2.13/1.32  tff(c_687, plain, (![A_86]: (k2_xboole_0(A_86, '#skF_2')='#skF_2' | ~r1_tarski(A_86, '#skF_3'))), inference(resolution, [status(thm)], [c_627, c_4])).
% 2.13/1.32  tff(c_698, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_434, c_687])).
% 2.13/1.32  tff(c_714, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_698, c_8])).
% 2.13/1.32  tff(c_777, plain, (![B_92, A_93]: (k1_tarski(B_92)=A_93 | k1_xboole_0=A_93 | ~r1_tarski(A_93, k1_tarski(B_92)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.32  tff(c_788, plain, (![A_93]: (k1_tarski('#skF_1')=A_93 | k1_xboole_0=A_93 | ~r1_tarski(A_93, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_404, c_777])).
% 2.13/1.32  tff(c_794, plain, (![A_94]: (A_94='#skF_2' | k1_xboole_0=A_94 | ~r1_tarski(A_94, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_788])).
% 2.13/1.32  tff(c_797, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_714, c_794])).
% 2.13/1.32  tff(c_812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_403, c_449, c_797])).
% 2.13/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.32  
% 2.13/1.32  Inference rules
% 2.13/1.32  ----------------------
% 2.13/1.32  #Ref     : 0
% 2.13/1.32  #Sup     : 181
% 2.13/1.32  #Fact    : 0
% 2.13/1.32  #Define  : 0
% 2.13/1.32  #Split   : 3
% 2.13/1.32  #Chain   : 0
% 2.13/1.32  #Close   : 0
% 2.13/1.32  
% 2.13/1.32  Ordering : KBO
% 2.13/1.32  
% 2.13/1.32  Simplification rules
% 2.13/1.32  ----------------------
% 2.13/1.32  #Subsume      : 2
% 2.13/1.32  #Demod        : 76
% 2.13/1.32  #Tautology    : 145
% 2.13/1.32  #SimpNegUnit  : 3
% 2.13/1.32  #BackRed      : 7
% 2.13/1.32  
% 2.13/1.32  #Partial instantiations: 0
% 2.13/1.32  #Strategies tried      : 1
% 2.13/1.32  
% 2.13/1.32  Timing (in seconds)
% 2.13/1.32  ----------------------
% 2.13/1.32  Preprocessing        : 0.28
% 2.13/1.32  Parsing              : 0.15
% 2.13/1.32  CNF conversion       : 0.02
% 2.13/1.32  Main loop            : 0.27
% 2.13/1.32  Inferencing          : 0.11
% 2.13/1.32  Reduction            : 0.08
% 2.13/1.32  Demodulation         : 0.06
% 2.13/1.32  BG Simplification    : 0.01
% 2.13/1.32  Subsumption          : 0.04
% 2.13/1.32  Abstraction          : 0.01
% 2.13/1.32  MUC search           : 0.00
% 2.13/1.32  Cooper               : 0.00
% 2.13/1.32  Total                : 0.59
% 2.13/1.32  Index Insertion      : 0.00
% 2.13/1.32  Index Deletion       : 0.00
% 2.13/1.32  Index Matching       : 0.00
% 2.13/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
