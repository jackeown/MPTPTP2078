%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:58 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 158 expanded)
%              Number of leaves         :   15 (  55 expanded)
%              Depth                    :    6
%              Number of atoms          :  102 ( 299 expanded)
%              Number of equality atoms :   64 ( 193 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_47,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_30,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_79,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_86,plain,(
    ! [B_19,C_20,A_21] :
      ( k2_tarski(B_19,C_20) = A_21
      | k1_tarski(C_20) = A_21
      | k1_tarski(B_19) = A_21
      | k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k2_tarski(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,(
    ! [A_3,A_21] :
      ( k2_tarski(A_3,A_3) = A_21
      | k1_tarski(A_3) = A_21
      | k1_tarski(A_3) = A_21
      | k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_86])).

tff(c_129,plain,(
    ! [A_28,A_29] :
      ( k1_tarski(A_28) = A_29
      | k1_tarski(A_28) = A_29
      | k1_tarski(A_28) = A_29
      | k1_xboole_0 = A_29
      | ~ r1_tarski(A_29,k1_tarski(A_28)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_132,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_79,c_129])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_58,c_58,c_58,c_132])).

tff(c_144,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_146,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_59,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_147,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_59])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_147])).

tff(c_151,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_35,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [B_5,C_6] : r1_tarski(k1_xboole_0,k2_tarski(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_18])).

tff(c_154,plain,(
    ! [A_10] : r1_tarski('#skF_1',k1_tarski(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_40])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_59])).

tff(c_163,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_194,plain,(
    ! [B_32,C_33,A_34] :
      ( k2_tarski(B_32,C_33) = A_34
      | k1_tarski(C_33) = A_34
      | k1_tarski(B_32) = A_34
      | k1_xboole_0 = A_34
      | ~ r1_tarski(A_34,k2_tarski(B_32,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_203,plain,(
    ! [A_3,A_34] :
      ( k2_tarski(A_3,A_3) = A_34
      | k1_tarski(A_3) = A_34
      | k1_tarski(A_3) = A_34
      | k1_xboole_0 = A_34
      | ~ r1_tarski(A_34,k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_194])).

tff(c_238,plain,(
    ! [A_42,A_43] :
      ( k1_tarski(A_42) = A_43
      | k1_tarski(A_42) = A_43
      | k1_tarski(A_42) = A_43
      | k1_xboole_0 = A_43
      | ~ r1_tarski(A_43,k1_tarski(A_42)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_203])).

tff(c_244,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_163,c_238])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_58,c_58,c_58,c_244])).

tff(c_258,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_22,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_285,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_22])).

tff(c_286,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_289,plain,(
    ! [A_10] : r1_tarski('#skF_1',k1_tarski(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_40])).

tff(c_257,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_257])).

tff(c_301,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_305,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_257])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_305])).

tff(c_310,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_26,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_333,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_310,c_26])).

tff(c_334,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_311,plain,(
    ! [A_10] : r1_tarski('#skF_3',k1_tarski(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_40])).

tff(c_337,plain,(
    ! [A_10] : r1_tarski('#skF_1',k1_tarski(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_311])).

tff(c_309,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_309])).

tff(c_350,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_352,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_309])).

tff(c_355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.34  
% 2.05/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.34  %$ r1_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.29/1.34  
% 2.29/1.34  %Foreground sorts:
% 2.29/1.34  
% 2.29/1.34  
% 2.29/1.34  %Background operators:
% 2.29/1.34  
% 2.29/1.34  
% 2.29/1.34  %Foreground operators:
% 2.29/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.34  
% 2.29/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.29/1.35  tff(f_55, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.29/1.35  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.29/1.35  tff(f_48, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.29/1.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.35  tff(c_24, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.29/1.35  tff(c_47, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_24])).
% 2.29/1.35  tff(c_20, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.29/1.35  tff(c_58, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_20])).
% 2.29/1.35  tff(c_30, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.29/1.35  tff(c_79, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.29/1.35  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.29/1.35  tff(c_86, plain, (![B_19, C_20, A_21]: (k2_tarski(B_19, C_20)=A_21 | k1_tarski(C_20)=A_21 | k1_tarski(B_19)=A_21 | k1_xboole_0=A_21 | ~r1_tarski(A_21, k2_tarski(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.35  tff(c_95, plain, (![A_3, A_21]: (k2_tarski(A_3, A_3)=A_21 | k1_tarski(A_3)=A_21 | k1_tarski(A_3)=A_21 | k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_86])).
% 2.29/1.35  tff(c_129, plain, (![A_28, A_29]: (k1_tarski(A_28)=A_29 | k1_tarski(A_28)=A_29 | k1_tarski(A_28)=A_29 | k1_xboole_0=A_29 | ~r1_tarski(A_29, k1_tarski(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_95])).
% 2.29/1.35  tff(c_132, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_79, c_129])).
% 2.29/1.35  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_58, c_58, c_58, c_132])).
% 2.29/1.35  tff(c_144, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_30])).
% 2.29/1.35  tff(c_146, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_144])).
% 2.29/1.35  tff(c_28, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.29/1.35  tff(c_59, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.29/1.35  tff(c_147, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_59])).
% 2.29/1.35  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_147])).
% 2.29/1.35  tff(c_151, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_144])).
% 2.29/1.35  tff(c_35, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.29/1.35  tff(c_18, plain, (![B_5, C_6]: (r1_tarski(k1_xboole_0, k2_tarski(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.35  tff(c_40, plain, (![A_10]: (r1_tarski(k1_xboole_0, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_18])).
% 2.29/1.35  tff(c_154, plain, (![A_10]: (r1_tarski('#skF_1', k1_tarski(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_40])).
% 2.29/1.35  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_59])).
% 2.29/1.35  tff(c_163, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_28])).
% 2.29/1.35  tff(c_194, plain, (![B_32, C_33, A_34]: (k2_tarski(B_32, C_33)=A_34 | k1_tarski(C_33)=A_34 | k1_tarski(B_32)=A_34 | k1_xboole_0=A_34 | ~r1_tarski(A_34, k2_tarski(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.35  tff(c_203, plain, (![A_3, A_34]: (k2_tarski(A_3, A_3)=A_34 | k1_tarski(A_3)=A_34 | k1_tarski(A_3)=A_34 | k1_xboole_0=A_34 | ~r1_tarski(A_34, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_194])).
% 2.29/1.35  tff(c_238, plain, (![A_42, A_43]: (k1_tarski(A_42)=A_43 | k1_tarski(A_42)=A_43 | k1_tarski(A_42)=A_43 | k1_xboole_0=A_43 | ~r1_tarski(A_43, k1_tarski(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_203])).
% 2.29/1.35  tff(c_244, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_163, c_238])).
% 2.29/1.35  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_58, c_58, c_58, c_244])).
% 2.29/1.35  tff(c_258, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_20])).
% 2.29/1.35  tff(c_22, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.29/1.35  tff(c_285, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_258, c_22])).
% 2.29/1.35  tff(c_286, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_285])).
% 2.29/1.35  tff(c_289, plain, (![A_10]: (r1_tarski('#skF_1', k1_tarski(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_40])).
% 2.29/1.35  tff(c_257, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_20])).
% 2.29/1.35  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_257])).
% 2.29/1.35  tff(c_301, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_285])).
% 2.29/1.35  tff(c_305, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_257])).
% 2.29/1.35  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_305])).
% 2.29/1.35  tff(c_310, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.29/1.35  tff(c_26, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.29/1.35  tff(c_333, plain, (k1_tarski('#skF_2')='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_310, c_310, c_26])).
% 2.29/1.35  tff(c_334, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_333])).
% 2.29/1.35  tff(c_311, plain, (![A_10]: (r1_tarski('#skF_3', k1_tarski(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_40])).
% 2.29/1.35  tff(c_337, plain, (![A_10]: (r1_tarski('#skF_1', k1_tarski(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_311])).
% 2.29/1.35  tff(c_309, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_24])).
% 2.29/1.35  tff(c_349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_337, c_309])).
% 2.29/1.35  tff(c_350, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_333])).
% 2.29/1.35  tff(c_352, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_309])).
% 2.29/1.35  tff(c_355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_352])).
% 2.29/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.35  
% 2.29/1.35  Inference rules
% 2.29/1.35  ----------------------
% 2.29/1.35  #Ref     : 0
% 2.29/1.35  #Sup     : 62
% 2.29/1.35  #Fact    : 0
% 2.29/1.35  #Define  : 0
% 2.29/1.35  #Split   : 8
% 2.29/1.35  #Chain   : 0
% 2.29/1.36  #Close   : 0
% 2.29/1.36  
% 2.29/1.36  Ordering : KBO
% 2.29/1.36  
% 2.29/1.36  Simplification rules
% 2.29/1.36  ----------------------
% 2.29/1.36  #Subsume      : 9
% 2.29/1.36  #Demod        : 55
% 2.29/1.36  #Tautology    : 39
% 2.29/1.36  #SimpNegUnit  : 5
% 2.29/1.36  #BackRed      : 18
% 2.29/1.36  
% 2.29/1.36  #Partial instantiations: 0
% 2.29/1.36  #Strategies tried      : 1
% 2.29/1.36  
% 2.29/1.36  Timing (in seconds)
% 2.29/1.36  ----------------------
% 2.29/1.36  Preprocessing        : 0.30
% 2.29/1.36  Parsing              : 0.15
% 2.29/1.36  CNF conversion       : 0.02
% 2.29/1.36  Main loop            : 0.24
% 2.29/1.36  Inferencing          : 0.08
% 2.29/1.36  Reduction            : 0.08
% 2.29/1.36  Demodulation         : 0.06
% 2.29/1.36  BG Simplification    : 0.02
% 2.29/1.36  Subsumption          : 0.05
% 2.29/1.36  Abstraction          : 0.01
% 2.29/1.36  MUC search           : 0.00
% 2.29/1.36  Cooper               : 0.00
% 2.29/1.36  Total                : 0.58
% 2.29/1.36  Index Insertion      : 0.00
% 2.29/1.36  Index Deletion       : 0.00
% 2.29/1.36  Index Matching       : 0.00
% 2.29/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
