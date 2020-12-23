%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:35 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   54 (  88 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :    5
%              Number of atoms          :   60 ( 124 expanded)
%              Number of equality atoms :   41 ( 100 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_213,plain,(
    ! [A_63,B_64] : k1_enumset1(A_63,A_63,B_64) = k2_tarski(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [E_7,B_2,C_3] : r2_hidden(E_7,k1_enumset1(E_7,B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_231,plain,(
    ! [A_65,B_66] : r2_hidden(A_65,k2_tarski(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_8])).

tff(c_234,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_231])).

tff(c_56,plain,(
    ! [A_26,B_27] : k1_enumset1(A_26,A_26,B_27) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    ! [B_28,A_29] : r2_hidden(B_28,k2_tarski(A_29,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4])).

tff(c_77,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_74])).

tff(c_38,plain,
    ( '#skF_3' != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_43,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_95,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(k1_tarski(A_36),B_37) = k1_tarski(A_36)
      | r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_79,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_106,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_79])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_113,plain,(
    ! [E_40,C_41,B_42,A_43] :
      ( E_40 = C_41
      | E_40 = B_42
      | E_40 = A_43
      | ~ r2_hidden(E_40,k1_enumset1(A_43,B_42,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_132,plain,(
    ! [E_44,B_45,A_46] :
      ( E_44 = B_45
      | E_44 = A_46
      | E_44 = A_46
      | ~ r2_hidden(E_44,k2_tarski(A_46,B_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_113])).

tff(c_146,plain,(
    ! [E_47,A_48] :
      ( E_47 = A_48
      | E_47 = A_48
      | E_47 = A_48
      | ~ r2_hidden(E_47,k1_tarski(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_132])).

tff(c_149,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_106,c_146])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_43,c_43,c_149])).

tff(c_157,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_158,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_40,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_180,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_157,c_158,c_40])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden(A_14,B_15)
      | k4_xboole_0(k1_tarski(A_14),B_15) != k1_tarski(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_184,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_32])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_184])).

tff(c_191,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_192,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( '#skF_3' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_267,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_191,c_192,c_42])).

tff(c_271,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_32])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:20:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 1.88/1.21  
% 1.88/1.21  %Foreground sorts:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Background operators:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Foreground operators:
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.88/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.88/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.88/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.88/1.21  
% 1.97/1.22  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.97/1.22  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.97/1.22  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.97/1.22  tff(f_57, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.97/1.22  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.97/1.22  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.97/1.22  tff(c_213, plain, (![A_63, B_64]: (k1_enumset1(A_63, A_63, B_64)=k2_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.97/1.22  tff(c_8, plain, (![E_7, B_2, C_3]: (r2_hidden(E_7, k1_enumset1(E_7, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.97/1.22  tff(c_231, plain, (![A_65, B_66]: (r2_hidden(A_65, k2_tarski(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_213, c_8])).
% 1.97/1.22  tff(c_234, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_231])).
% 1.97/1.22  tff(c_56, plain, (![A_26, B_27]: (k1_enumset1(A_26, A_26, B_27)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.97/1.22  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.97/1.22  tff(c_74, plain, (![B_28, A_29]: (r2_hidden(B_28, k2_tarski(A_29, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_4])).
% 1.97/1.22  tff(c_77, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_74])).
% 1.97/1.22  tff(c_38, plain, ('#skF_3'!='#skF_4' | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.97/1.22  tff(c_43, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_38])).
% 1.97/1.22  tff(c_95, plain, (![A_36, B_37]: (k4_xboole_0(k1_tarski(A_36), B_37)=k1_tarski(A_36) | r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.22  tff(c_36, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.97/1.22  tff(c_79, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 1.97/1.22  tff(c_106, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_79])).
% 1.97/1.22  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.97/1.22  tff(c_113, plain, (![E_40, C_41, B_42, A_43]: (E_40=C_41 | E_40=B_42 | E_40=A_43 | ~r2_hidden(E_40, k1_enumset1(A_43, B_42, C_41)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.97/1.22  tff(c_132, plain, (![E_44, B_45, A_46]: (E_44=B_45 | E_44=A_46 | E_44=A_46 | ~r2_hidden(E_44, k2_tarski(A_46, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_113])).
% 1.97/1.22  tff(c_146, plain, (![E_47, A_48]: (E_47=A_48 | E_47=A_48 | E_47=A_48 | ~r2_hidden(E_47, k1_tarski(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_132])).
% 1.97/1.22  tff(c_149, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_106, c_146])).
% 1.97/1.22  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_43, c_43, c_149])).
% 1.97/1.22  tff(c_157, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_36])).
% 1.97/1.22  tff(c_158, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 1.97/1.22  tff(c_40, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.97/1.22  tff(c_180, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_157, c_158, c_40])).
% 1.97/1.22  tff(c_32, plain, (![A_14, B_15]: (~r2_hidden(A_14, B_15) | k4_xboole_0(k1_tarski(A_14), B_15)!=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.22  tff(c_184, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_180, c_32])).
% 1.97/1.22  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_184])).
% 1.97/1.22  tff(c_191, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 1.97/1.22  tff(c_192, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 1.97/1.22  tff(c_42, plain, ('#skF_3'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.97/1.22  tff(c_267, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_191, c_192, c_42])).
% 1.97/1.22  tff(c_271, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_267, c_32])).
% 1.97/1.22  tff(c_283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_234, c_271])).
% 1.97/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  Inference rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Ref     : 0
% 1.97/1.22  #Sup     : 56
% 1.97/1.22  #Fact    : 0
% 1.97/1.22  #Define  : 0
% 1.97/1.22  #Split   : 2
% 1.97/1.22  #Chain   : 0
% 1.97/1.22  #Close   : 0
% 1.97/1.22  
% 1.97/1.22  Ordering : KBO
% 1.97/1.22  
% 1.97/1.22  Simplification rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Subsume      : 3
% 1.97/1.22  #Demod        : 19
% 1.97/1.22  #Tautology    : 40
% 1.97/1.22  #SimpNegUnit  : 1
% 1.97/1.22  #BackRed      : 0
% 1.97/1.22  
% 1.97/1.22  #Partial instantiations: 0
% 1.97/1.22  #Strategies tried      : 1
% 1.97/1.22  
% 1.97/1.22  Timing (in seconds)
% 1.97/1.22  ----------------------
% 1.97/1.23  Preprocessing        : 0.29
% 1.97/1.23  Parsing              : 0.14
% 1.97/1.23  CNF conversion       : 0.02
% 1.97/1.23  Main loop            : 0.17
% 1.97/1.23  Inferencing          : 0.06
% 1.97/1.23  Reduction            : 0.05
% 1.97/1.23  Demodulation         : 0.04
% 1.97/1.23  BG Simplification    : 0.01
% 1.97/1.23  Subsumption          : 0.03
% 1.97/1.23  Abstraction          : 0.01
% 1.97/1.23  MUC search           : 0.00
% 1.97/1.23  Cooper               : 0.00
% 1.97/1.23  Total                : 0.50
% 1.97/1.23  Index Insertion      : 0.00
% 1.97/1.23  Index Deletion       : 0.00
% 1.97/1.23  Index Matching       : 0.00
% 1.97/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
