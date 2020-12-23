%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:35 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   51 (  86 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :    5
%              Number of atoms          :   50 ( 106 expanded)
%              Number of equality atoms :   37 (  88 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_12,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_168,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k2_xboole_0(A_36,B_37)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_175,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_168])).

tff(c_328,plain,(
    ! [A_55,B_56] :
      ( ~ r2_hidden(A_55,B_56)
      | k4_xboole_0(k1_tarski(A_55),B_56) != k1_tarski(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_341,plain,(
    ! [A_55] :
      ( ~ r2_hidden(A_55,k1_tarski(A_55))
      | k1_tarski(A_55) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_328])).

tff(c_350,plain,(
    ! [A_55] : k1_tarski(A_55) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_341])).

tff(c_46,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_129,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden(A_31,B_32)
      | k4_xboole_0(k1_tarski(A_31),B_32) != k1_tarski(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_136,plain,(
    ! [A_31] :
      ( ~ r2_hidden(A_31,k1_tarski(A_31))
      | k1_tarski(A_31) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_129])).

tff(c_143,plain,(
    ! [A_31] : k1_tarski(A_31) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_136])).

tff(c_30,plain,
    ( '#skF_3' != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_35,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_81,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(k1_tarski(A_29),B_30) = k1_tarski(A_29)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_80,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_108,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_80])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_114,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_108,c_10])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_114])).

tff(c_119,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_120,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_32,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_146,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_53,c_119,c_120,c_32])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_146])).

tff(c_148,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_149,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( '#skF_3' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_194,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_148,c_148,c_149,c_34])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_350,c_194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:33:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.23  
% 1.97/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.24  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.97/1.24  
% 1.97/1.24  %Foreground sorts:
% 1.97/1.24  
% 1.97/1.24  
% 1.97/1.24  %Background operators:
% 1.97/1.24  
% 1.97/1.24  
% 1.97/1.24  %Foreground operators:
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.24  tff('#skF_6', type, '#skF_6': $i).
% 1.97/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.97/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.24  
% 2.03/1.25  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.03/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.03/1.25  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.03/1.25  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.03/1.25  tff(f_56, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.03/1.25  tff(c_12, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.25  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.25  tff(c_168, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k2_xboole_0(A_36, B_37))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.25  tff(c_175, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_168])).
% 2.03/1.25  tff(c_328, plain, (![A_55, B_56]: (~r2_hidden(A_55, B_56) | k4_xboole_0(k1_tarski(A_55), B_56)!=k1_tarski(A_55))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.03/1.25  tff(c_341, plain, (![A_55]: (~r2_hidden(A_55, k1_tarski(A_55)) | k1_tarski(A_55)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_175, c_328])).
% 2.03/1.25  tff(c_350, plain, (![A_55]: (k1_tarski(A_55)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_341])).
% 2.03/1.25  tff(c_46, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.25  tff(c_53, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_46])).
% 2.03/1.25  tff(c_129, plain, (![A_31, B_32]: (~r2_hidden(A_31, B_32) | k4_xboole_0(k1_tarski(A_31), B_32)!=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.03/1.25  tff(c_136, plain, (![A_31]: (~r2_hidden(A_31, k1_tarski(A_31)) | k1_tarski(A_31)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_53, c_129])).
% 2.03/1.25  tff(c_143, plain, (![A_31]: (k1_tarski(A_31)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_136])).
% 2.03/1.25  tff(c_30, plain, ('#skF_3'!='#skF_4' | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.25  tff(c_35, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_30])).
% 2.03/1.25  tff(c_81, plain, (![A_29, B_30]: (k4_xboole_0(k1_tarski(A_29), B_30)=k1_tarski(A_29) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.03/1.25  tff(c_28, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.25  tff(c_80, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 2.03/1.25  tff(c_108, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_80])).
% 2.03/1.25  tff(c_10, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.25  tff(c_114, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_108, c_10])).
% 2.03/1.25  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_114])).
% 2.03/1.25  tff(c_119, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_28])).
% 2.03/1.25  tff(c_120, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.03/1.25  tff(c_32, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.25  tff(c_146, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_53, c_119, c_120, c_32])).
% 2.03/1.25  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_146])).
% 2.03/1.25  tff(c_148, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_30])).
% 2.03/1.25  tff(c_149, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.03/1.25  tff(c_34, plain, ('#skF_3'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.25  tff(c_194, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_175, c_148, c_148, c_149, c_34])).
% 2.03/1.25  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_350, c_194])).
% 2.03/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.25  
% 2.03/1.25  Inference rules
% 2.03/1.25  ----------------------
% 2.03/1.25  #Ref     : 0
% 2.03/1.25  #Sup     : 72
% 2.03/1.25  #Fact    : 0
% 2.03/1.25  #Define  : 0
% 2.03/1.25  #Split   : 2
% 2.03/1.25  #Chain   : 0
% 2.03/1.25  #Close   : 0
% 2.03/1.25  
% 2.03/1.25  Ordering : KBO
% 2.03/1.25  
% 2.03/1.25  Simplification rules
% 2.03/1.25  ----------------------
% 2.03/1.25  #Subsume      : 3
% 2.03/1.25  #Demod        : 31
% 2.03/1.25  #Tautology    : 49
% 2.03/1.25  #SimpNegUnit  : 3
% 2.03/1.25  #BackRed      : 1
% 2.03/1.25  
% 2.03/1.25  #Partial instantiations: 0
% 2.03/1.25  #Strategies tried      : 1
% 2.03/1.25  
% 2.03/1.25  Timing (in seconds)
% 2.03/1.25  ----------------------
% 2.03/1.25  Preprocessing        : 0.29
% 2.03/1.25  Parsing              : 0.15
% 2.03/1.25  CNF conversion       : 0.02
% 2.03/1.25  Main loop            : 0.19
% 2.03/1.25  Inferencing          : 0.07
% 2.03/1.25  Reduction            : 0.05
% 2.03/1.25  Demodulation         : 0.04
% 2.03/1.25  BG Simplification    : 0.01
% 2.03/1.25  Subsumption          : 0.03
% 2.03/1.25  Abstraction          : 0.01
% 2.03/1.25  MUC search           : 0.00
% 2.03/1.25  Cooper               : 0.00
% 2.03/1.25  Total                : 0.50
% 2.03/1.25  Index Insertion      : 0.00
% 2.03/1.25  Index Deletion       : 0.00
% 2.03/1.25  Index Matching       : 0.00
% 2.03/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
