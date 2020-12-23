%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:36 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   55 (  81 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :    5
%              Number of atoms          :   56 ( 107 expanded)
%              Number of equality atoms :   31 (  73 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_10,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,
    ( '#skF_3' != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_37,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_56,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(k1_tarski(A_28),B_29)
      | r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(k1_tarski(A_43),B_44) = k1_tarski(A_43)
      | r2_hidden(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_56,c_4])).

tff(c_30,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_102,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_120,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_102])).

tff(c_8,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_124,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_120,c_8])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_124])).

tff(c_129,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_130,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_131,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_131])).

tff(c_142,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_152,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_129,c_142])).

tff(c_65,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | k4_xboole_0(A_30,B_31) != A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( ~ r2_hidden(A_16,B_17)
      | ~ r1_xboole_0(k1_tarski(A_16),B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_158,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden(A_45,B_46)
      | k4_xboole_0(k1_tarski(A_45),B_46) != k1_tarski(A_45) ) ),
    inference(resolution,[status(thm)],[c_65,c_26])).

tff(c_161,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_158])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_161])).

tff(c_169,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_170,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( '#skF_3' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_227,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_169,c_170,c_36])).

tff(c_202,plain,(
    ! [A_55,B_56] :
      ( r1_xboole_0(A_55,B_56)
      | k4_xboole_0(A_55,B_56) != A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_250,plain,(
    ! [A_66,B_67] :
      ( ~ r2_hidden(A_66,B_67)
      | k4_xboole_0(k1_tarski(A_66),B_67) != k1_tarski(A_66) ) ),
    inference(resolution,[status(thm)],[c_202,c_26])).

tff(c_253,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_250])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.21  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.91/1.21  
% 1.91/1.21  %Foreground sorts:
% 1.91/1.21  
% 1.91/1.21  
% 1.91/1.21  %Background operators:
% 1.91/1.21  
% 1.91/1.21  
% 1.91/1.21  %Foreground operators:
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.91/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.91/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.21  
% 2.01/1.22  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.01/1.22  tff(f_60, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.01/1.22  tff(f_54, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.01/1.22  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.01/1.22  tff(f_49, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.01/1.22  tff(c_10, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.01/1.22  tff(c_32, plain, ('#skF_3'!='#skF_4' | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.01/1.22  tff(c_37, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_32])).
% 2.01/1.22  tff(c_56, plain, (![A_28, B_29]: (r1_xboole_0(k1_tarski(A_28), B_29) | r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.01/1.22  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.22  tff(c_105, plain, (![A_43, B_44]: (k4_xboole_0(k1_tarski(A_43), B_44)=k1_tarski(A_43) | r2_hidden(A_43, B_44))), inference(resolution, [status(thm)], [c_56, c_4])).
% 2.01/1.22  tff(c_30, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.01/1.22  tff(c_102, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.01/1.22  tff(c_120, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_102])).
% 2.01/1.22  tff(c_8, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.01/1.22  tff(c_124, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_120, c_8])).
% 2.01/1.22  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_124])).
% 2.01/1.22  tff(c_129, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_30])).
% 2.01/1.22  tff(c_130, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.01/1.22  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.01/1.22  tff(c_131, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.01/1.22  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_131])).
% 2.01/1.22  tff(c_142, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_34])).
% 2.01/1.22  tff(c_152, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_129, c_142])).
% 2.01/1.22  tff(c_65, plain, (![A_30, B_31]: (r1_xboole_0(A_30, B_31) | k4_xboole_0(A_30, B_31)!=A_30)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.22  tff(c_26, plain, (![A_16, B_17]: (~r2_hidden(A_16, B_17) | ~r1_xboole_0(k1_tarski(A_16), B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.01/1.22  tff(c_158, plain, (![A_45, B_46]: (~r2_hidden(A_45, B_46) | k4_xboole_0(k1_tarski(A_45), B_46)!=k1_tarski(A_45))), inference(resolution, [status(thm)], [c_65, c_26])).
% 2.01/1.22  tff(c_161, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_152, c_158])).
% 2.01/1.22  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_161])).
% 2.01/1.22  tff(c_169, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 2.01/1.22  tff(c_170, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 2.01/1.22  tff(c_36, plain, ('#skF_3'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.01/1.22  tff(c_227, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_169, c_170, c_36])).
% 2.01/1.22  tff(c_202, plain, (![A_55, B_56]: (r1_xboole_0(A_55, B_56) | k4_xboole_0(A_55, B_56)!=A_55)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.22  tff(c_250, plain, (![A_66, B_67]: (~r2_hidden(A_66, B_67) | k4_xboole_0(k1_tarski(A_66), B_67)!=k1_tarski(A_66))), inference(resolution, [status(thm)], [c_202, c_26])).
% 2.01/1.22  tff(c_253, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_227, c_250])).
% 2.01/1.22  tff(c_257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_253])).
% 2.01/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.22  
% 2.01/1.22  Inference rules
% 2.01/1.22  ----------------------
% 2.01/1.22  #Ref     : 0
% 2.01/1.22  #Sup     : 50
% 2.01/1.22  #Fact    : 0
% 2.01/1.22  #Define  : 0
% 2.01/1.22  #Split   : 3
% 2.01/1.22  #Chain   : 0
% 2.01/1.22  #Close   : 0
% 2.01/1.22  
% 2.01/1.22  Ordering : KBO
% 2.01/1.22  
% 2.01/1.22  Simplification rules
% 2.01/1.22  ----------------------
% 2.01/1.22  #Subsume      : 1
% 2.01/1.22  #Demod        : 10
% 2.01/1.22  #Tautology    : 43
% 2.01/1.22  #SimpNegUnit  : 1
% 2.01/1.22  #BackRed      : 0
% 2.01/1.22  
% 2.01/1.22  #Partial instantiations: 0
% 2.01/1.22  #Strategies tried      : 1
% 2.01/1.22  
% 2.01/1.22  Timing (in seconds)
% 2.01/1.22  ----------------------
% 2.01/1.22  Preprocessing        : 0.30
% 2.01/1.22  Parsing              : 0.15
% 2.01/1.22  CNF conversion       : 0.02
% 2.01/1.22  Main loop            : 0.16
% 2.01/1.22  Inferencing          : 0.06
% 2.01/1.22  Reduction            : 0.05
% 2.01/1.22  Demodulation         : 0.03
% 2.01/1.22  BG Simplification    : 0.01
% 2.01/1.22  Subsumption          : 0.02
% 2.01/1.22  Abstraction          : 0.01
% 2.01/1.22  MUC search           : 0.00
% 2.01/1.22  Cooper               : 0.00
% 2.01/1.22  Total                : 0.48
% 2.01/1.22  Index Insertion      : 0.00
% 2.01/1.22  Index Deletion       : 0.00
% 2.01/1.22  Index Matching       : 0.00
% 2.01/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
