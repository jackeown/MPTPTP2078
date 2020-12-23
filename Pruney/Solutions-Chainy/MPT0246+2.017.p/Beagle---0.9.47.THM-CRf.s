%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:02 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 106 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 210 expanded)
%              Number of equality atoms :   45 ( 154 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_34,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_52,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_1'(A_43),A_43)
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [C_37] :
      ( C_37 = '#skF_5'
      | ~ r2_hidden(C_37,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_60,plain,
    ( '#skF_1'('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_30])).

tff(c_64,plain,(
    '#skF_1'('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_60])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2])).

tff(c_71,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_68])).

tff(c_120,plain,(
    ! [A_56,B_57] :
      ( '#skF_2'(A_56,B_57) = A_56
      | r2_hidden('#skF_3'(A_56,B_57),B_57)
      | k1_tarski(A_56) = B_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_133,plain,(
    ! [A_60] :
      ( '#skF_3'(A_60,'#skF_4') = '#skF_5'
      | '#skF_2'(A_60,'#skF_4') = A_60
      | k1_tarski(A_60) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_120,c_30])).

tff(c_154,plain,
    ( '#skF_3'('#skF_5','#skF_4') = '#skF_5'
    | '#skF_2'('#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_34])).

tff(c_156,plain,(
    '#skF_2'('#skF_5','#skF_4') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_2'(A_3,B_4),B_4)
      | '#skF_3'(A_3,B_4) != A_3
      | k1_tarski(A_3) = B_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_160,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | '#skF_3'('#skF_5','#skF_4') != '#skF_5'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_8])).

tff(c_164,plain,
    ( '#skF_3'('#skF_5','#skF_4') != '#skF_5'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_160])).

tff(c_165,plain,(
    '#skF_3'('#skF_5','#skF_4') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_164])).

tff(c_209,plain,(
    ! [A_68,B_69] :
      ( ~ r2_hidden('#skF_2'(A_68,B_69),B_69)
      | r2_hidden('#skF_3'(A_68,B_69),B_69)
      | k1_tarski(A_68) = B_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_224,plain,(
    ! [A_70] :
      ( '#skF_3'(A_70,'#skF_4') = '#skF_5'
      | ~ r2_hidden('#skF_2'(A_70,'#skF_4'),'#skF_4')
      | k1_tarski(A_70) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_209,c_30])).

tff(c_230,plain,
    ( '#skF_3'('#skF_5','#skF_4') = '#skF_5'
    | ~ r2_hidden('#skF_5','#skF_4')
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_224])).

tff(c_233,plain,
    ( '#skF_3'('#skF_5','#skF_4') = '#skF_5'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_230])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_165,c_233])).

tff(c_237,plain,(
    '#skF_2'('#skF_5','#skF_4') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_236,plain,(
    '#skF_3'('#skF_5','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( '#skF_2'(A_3,B_4) = A_3
      | '#skF_3'(A_3,B_4) != A_3
      | k1_tarski(A_3) = B_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_257,plain,
    ( '#skF_2'('#skF_5','#skF_4') = '#skF_5'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_10])).

tff(c_266,plain,(
    '#skF_2'('#skF_5','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_257])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.62  
% 2.43/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.62  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.43/1.62  
% 2.43/1.62  %Foreground sorts:
% 2.43/1.62  
% 2.43/1.62  
% 2.43/1.62  %Background operators:
% 2.43/1.62  
% 2.43/1.62  
% 2.43/1.62  %Foreground operators:
% 2.43/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.43/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.43/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.43/1.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.43/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.43/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.62  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.43/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.43/1.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.43/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.62  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.43/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.43/1.62  
% 2.64/1.64  tff(f_69, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.64/1.64  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.64/1.64  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.64/1.64  tff(c_34, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.64/1.64  tff(c_32, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.64/1.64  tff(c_52, plain, (![A_43]: (r2_hidden('#skF_1'(A_43), A_43) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.64  tff(c_30, plain, (![C_37]: (C_37='#skF_5' | ~r2_hidden(C_37, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.64/1.64  tff(c_60, plain, ('#skF_1'('#skF_4')='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_52, c_30])).
% 2.64/1.64  tff(c_64, plain, ('#skF_1'('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_32, c_60])).
% 2.64/1.64  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.64  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_4') | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_64, c_2])).
% 2.64/1.64  tff(c_71, plain, (r2_hidden('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_68])).
% 2.64/1.64  tff(c_120, plain, (![A_56, B_57]: ('#skF_2'(A_56, B_57)=A_56 | r2_hidden('#skF_3'(A_56, B_57), B_57) | k1_tarski(A_56)=B_57)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.64/1.64  tff(c_133, plain, (![A_60]: ('#skF_3'(A_60, '#skF_4')='#skF_5' | '#skF_2'(A_60, '#skF_4')=A_60 | k1_tarski(A_60)='#skF_4')), inference(resolution, [status(thm)], [c_120, c_30])).
% 2.64/1.64  tff(c_154, plain, ('#skF_3'('#skF_5', '#skF_4')='#skF_5' | '#skF_2'('#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_133, c_34])).
% 2.64/1.64  tff(c_156, plain, ('#skF_2'('#skF_5', '#skF_4')='#skF_5'), inference(splitLeft, [status(thm)], [c_154])).
% 2.64/1.64  tff(c_8, plain, (![A_3, B_4]: (~r2_hidden('#skF_2'(A_3, B_4), B_4) | '#skF_3'(A_3, B_4)!=A_3 | k1_tarski(A_3)=B_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.64/1.64  tff(c_160, plain, (~r2_hidden('#skF_5', '#skF_4') | '#skF_3'('#skF_5', '#skF_4')!='#skF_5' | k1_tarski('#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_156, c_8])).
% 2.64/1.64  tff(c_164, plain, ('#skF_3'('#skF_5', '#skF_4')!='#skF_5' | k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_160])).
% 2.64/1.64  tff(c_165, plain, ('#skF_3'('#skF_5', '#skF_4')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_34, c_164])).
% 2.64/1.64  tff(c_209, plain, (![A_68, B_69]: (~r2_hidden('#skF_2'(A_68, B_69), B_69) | r2_hidden('#skF_3'(A_68, B_69), B_69) | k1_tarski(A_68)=B_69)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.64/1.64  tff(c_224, plain, (![A_70]: ('#skF_3'(A_70, '#skF_4')='#skF_5' | ~r2_hidden('#skF_2'(A_70, '#skF_4'), '#skF_4') | k1_tarski(A_70)='#skF_4')), inference(resolution, [status(thm)], [c_209, c_30])).
% 2.64/1.64  tff(c_230, plain, ('#skF_3'('#skF_5', '#skF_4')='#skF_5' | ~r2_hidden('#skF_5', '#skF_4') | k1_tarski('#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_156, c_224])).
% 2.64/1.64  tff(c_233, plain, ('#skF_3'('#skF_5', '#skF_4')='#skF_5' | k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_230])).
% 2.64/1.64  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_165, c_233])).
% 2.64/1.64  tff(c_237, plain, ('#skF_2'('#skF_5', '#skF_4')!='#skF_5'), inference(splitRight, [status(thm)], [c_154])).
% 2.64/1.64  tff(c_236, plain, ('#skF_3'('#skF_5', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_154])).
% 2.64/1.64  tff(c_10, plain, (![A_3, B_4]: ('#skF_2'(A_3, B_4)=A_3 | '#skF_3'(A_3, B_4)!=A_3 | k1_tarski(A_3)=B_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.64/1.64  tff(c_257, plain, ('#skF_2'('#skF_5', '#skF_4')='#skF_5' | k1_tarski('#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_236, c_10])).
% 2.64/1.64  tff(c_266, plain, ('#skF_2'('#skF_5', '#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_34, c_257])).
% 2.64/1.64  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_266])).
% 2.64/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.64  
% 2.64/1.64  Inference rules
% 2.64/1.64  ----------------------
% 2.64/1.64  #Ref     : 0
% 2.64/1.64  #Sup     : 50
% 2.64/1.64  #Fact    : 0
% 2.64/1.64  #Define  : 0
% 2.64/1.64  #Split   : 1
% 2.64/1.64  #Chain   : 0
% 2.64/1.64  #Close   : 0
% 2.64/1.64  
% 2.64/1.64  Ordering : KBO
% 2.64/1.64  
% 2.64/1.64  Simplification rules
% 2.64/1.64  ----------------------
% 2.64/1.64  #Subsume      : 0
% 2.64/1.64  #Demod        : 9
% 2.64/1.64  #Tautology    : 31
% 2.64/1.64  #SimpNegUnit  : 8
% 2.64/1.64  #BackRed      : 0
% 2.64/1.64  
% 2.64/1.64  #Partial instantiations: 0
% 2.64/1.64  #Strategies tried      : 1
% 2.64/1.64  
% 2.64/1.64  Timing (in seconds)
% 2.64/1.64  ----------------------
% 2.64/1.64  Preprocessing        : 0.50
% 2.64/1.64  Parsing              : 0.25
% 2.64/1.64  CNF conversion       : 0.04
% 2.64/1.64  Main loop            : 0.31
% 2.64/1.64  Inferencing          : 0.11
% 2.64/1.64  Reduction            : 0.08
% 2.64/1.64  Demodulation         : 0.05
% 2.64/1.64  BG Simplification    : 0.03
% 2.64/1.64  Subsumption          : 0.05
% 2.64/1.64  Abstraction          : 0.02
% 2.64/1.64  MUC search           : 0.00
% 2.64/1.64  Cooper               : 0.00
% 2.64/1.64  Total                : 0.85
% 2.64/1.65  Index Insertion      : 0.00
% 2.64/1.65  Index Deletion       : 0.00
% 2.64/1.65  Index Matching       : 0.00
% 2.64/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
