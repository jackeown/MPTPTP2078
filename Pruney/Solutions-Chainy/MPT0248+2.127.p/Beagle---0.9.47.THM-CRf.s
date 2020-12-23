%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:22 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :   60 (  89 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 193 expanded)
%              Number of equality atoms :   41 ( 156 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_50,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_61,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,
    ( k1_xboole_0 != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_71,plain,(
    k1_tarski('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_72,plain,(
    ! [A_33,B_34] : r1_tarski(A_33,k2_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_72])).

tff(c_430,plain,(
    ! [B_74,A_75] :
      ( k1_tarski(B_74) = A_75
      | k1_xboole_0 = A_75
      | ~ r1_tarski(A_75,k1_tarski(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_440,plain,
    ( k1_tarski('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_75,c_430])).

tff(c_451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_71,c_440])).

tff(c_452,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_453,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( k1_tarski('#skF_4') != '#skF_6'
    | k1_tarski('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_474,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_453,c_52])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_454,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_54])).

tff(c_655,plain,(
    ! [D_90,B_91,A_92] :
      ( ~ r2_hidden(D_90,B_91)
      | r2_hidden(D_90,k2_xboole_0(A_92,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_676,plain,(
    ! [D_90] :
      ( ~ r2_hidden(D_90,'#skF_6')
      | r2_hidden(D_90,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_655])).

tff(c_701,plain,(
    ! [A_98,B_99] :
      ( ~ r2_hidden('#skF_1'(A_98,B_99),B_99)
      | r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_863,plain,(
    ! [A_112] :
      ( r1_tarski(A_112,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_112,'#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_676,c_701])).

tff(c_868,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_863])).

tff(c_902,plain,(
    ! [B_116,A_117] :
      ( k1_tarski(B_116) = A_117
      | k1_xboole_0 = A_117
      | ~ r1_tarski(A_117,k1_tarski(B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_909,plain,(
    ! [A_117] :
      ( k1_tarski('#skF_4') = A_117
      | k1_xboole_0 = A_117
      | ~ r1_tarski(A_117,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_902])).

tff(c_919,plain,(
    ! [A_118] :
      ( A_118 = '#skF_5'
      | k1_xboole_0 = A_118
      | ~ r1_tarski(A_118,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_909])).

tff(c_922,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_868,c_919])).

tff(c_934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_474,c_922])).

tff(c_935,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_936,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_28,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_937,plain,(
    ! [A_14] : r1_tarski('#skF_5',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_28])).

tff(c_960,plain,(
    ! [A_124,B_125] :
      ( k2_xboole_0(A_124,B_125) = B_125
      | ~ r1_tarski(A_124,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_972,plain,(
    ! [A_14] : k2_xboole_0('#skF_5',A_14) = A_14 ),
    inference(resolution,[status(thm)],[c_937,c_960])).

tff(c_973,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_54])).

tff(c_975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_935,c_973])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:20:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.89  
% 3.29/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.90  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.29/1.90  
% 3.29/1.90  %Foreground sorts:
% 3.29/1.90  
% 3.29/1.90  
% 3.29/1.90  %Background operators:
% 3.29/1.90  
% 3.29/1.90  
% 3.29/1.90  %Foreground operators:
% 3.29/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.90  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.90  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.29/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.29/1.90  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.90  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.29/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.29/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.29/1.90  
% 3.59/1.91  tff(f_84, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.59/1.91  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.59/1.91  tff(f_63, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.59/1.91  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.59/1.91  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.59/1.91  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.59/1.91  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.59/1.91  tff(c_50, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.59/1.91  tff(c_61, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_50])).
% 3.59/1.91  tff(c_48, plain, (k1_xboole_0!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.59/1.91  tff(c_71, plain, (k1_tarski('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_48])).
% 3.59/1.91  tff(c_54, plain, (k2_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.59/1.91  tff(c_72, plain, (![A_33, B_34]: (r1_tarski(A_33, k2_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.59/1.91  tff(c_75, plain, (r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_72])).
% 3.59/1.91  tff(c_430, plain, (![B_74, A_75]: (k1_tarski(B_74)=A_75 | k1_xboole_0=A_75 | ~r1_tarski(A_75, k1_tarski(B_74)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.59/1.91  tff(c_440, plain, (k1_tarski('#skF_4')='#skF_5' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_75, c_430])).
% 3.59/1.91  tff(c_451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_71, c_440])).
% 3.59/1.91  tff(c_452, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 3.59/1.91  tff(c_453, plain, (k1_tarski('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_48])).
% 3.59/1.91  tff(c_52, plain, (k1_tarski('#skF_4')!='#skF_6' | k1_tarski('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.59/1.91  tff(c_474, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_453, c_453, c_52])).
% 3.59/1.91  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.91  tff(c_454, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_453, c_54])).
% 3.59/1.91  tff(c_655, plain, (![D_90, B_91, A_92]: (~r2_hidden(D_90, B_91) | r2_hidden(D_90, k2_xboole_0(A_92, B_91)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.59/1.91  tff(c_676, plain, (![D_90]: (~r2_hidden(D_90, '#skF_6') | r2_hidden(D_90, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_454, c_655])).
% 3.59/1.91  tff(c_701, plain, (![A_98, B_99]: (~r2_hidden('#skF_1'(A_98, B_99), B_99) | r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.59/1.91  tff(c_863, plain, (![A_112]: (r1_tarski(A_112, '#skF_5') | ~r2_hidden('#skF_1'(A_112, '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_676, c_701])).
% 3.59/1.91  tff(c_868, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_863])).
% 3.59/1.91  tff(c_902, plain, (![B_116, A_117]: (k1_tarski(B_116)=A_117 | k1_xboole_0=A_117 | ~r1_tarski(A_117, k1_tarski(B_116)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.59/1.91  tff(c_909, plain, (![A_117]: (k1_tarski('#skF_4')=A_117 | k1_xboole_0=A_117 | ~r1_tarski(A_117, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_453, c_902])).
% 3.59/1.91  tff(c_919, plain, (![A_118]: (A_118='#skF_5' | k1_xboole_0=A_118 | ~r1_tarski(A_118, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_453, c_909])).
% 3.59/1.91  tff(c_922, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_868, c_919])).
% 3.59/1.91  tff(c_934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_452, c_474, c_922])).
% 3.59/1.91  tff(c_935, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 3.59/1.91  tff(c_936, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 3.59/1.91  tff(c_28, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.59/1.91  tff(c_937, plain, (![A_14]: (r1_tarski('#skF_5', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_936, c_28])).
% 3.59/1.91  tff(c_960, plain, (![A_124, B_125]: (k2_xboole_0(A_124, B_125)=B_125 | ~r1_tarski(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.59/1.91  tff(c_972, plain, (![A_14]: (k2_xboole_0('#skF_5', A_14)=A_14)), inference(resolution, [status(thm)], [c_937, c_960])).
% 3.59/1.91  tff(c_973, plain, (k1_tarski('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_972, c_54])).
% 3.59/1.91  tff(c_975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_935, c_973])).
% 3.59/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.91  
% 3.59/1.91  Inference rules
% 3.59/1.91  ----------------------
% 3.59/1.92  #Ref     : 0
% 3.59/1.92  #Sup     : 221
% 3.59/1.92  #Fact    : 0
% 3.59/1.92  #Define  : 0
% 3.59/1.92  #Split   : 3
% 3.59/1.92  #Chain   : 0
% 3.59/1.92  #Close   : 0
% 3.59/1.92  
% 3.59/1.92  Ordering : KBO
% 3.59/1.92  
% 3.59/1.92  Simplification rules
% 3.59/1.92  ----------------------
% 3.59/1.92  #Subsume      : 9
% 3.59/1.92  #Demod        : 113
% 3.59/1.92  #Tautology    : 168
% 3.59/1.92  #SimpNegUnit  : 3
% 3.59/1.92  #BackRed      : 10
% 3.59/1.92  
% 3.59/1.92  #Partial instantiations: 0
% 3.59/1.92  #Strategies tried      : 1
% 3.59/1.92  
% 3.59/1.92  Timing (in seconds)
% 3.59/1.92  ----------------------
% 3.59/1.92  Preprocessing        : 0.50
% 3.59/1.92  Parsing              : 0.26
% 3.59/1.92  CNF conversion       : 0.03
% 3.59/1.92  Main loop            : 0.54
% 3.59/1.92  Inferencing          : 0.20
% 3.59/1.92  Reduction            : 0.17
% 3.59/1.92  Demodulation         : 0.13
% 3.59/1.92  BG Simplification    : 0.03
% 3.59/1.92  Subsumption          : 0.08
% 3.59/1.92  Abstraction          : 0.03
% 3.59/1.92  MUC search           : 0.00
% 3.59/1.92  Cooper               : 0.00
% 3.59/1.92  Total                : 1.09
% 3.59/1.92  Index Insertion      : 0.00
% 3.59/1.92  Index Deletion       : 0.00
% 3.59/1.92  Index Matching       : 0.00
% 3.59/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
