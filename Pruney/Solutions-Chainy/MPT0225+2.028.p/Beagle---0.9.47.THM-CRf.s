%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:34 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 101 expanded)
%              Number of leaves         :   26 (  46 expanded)
%              Depth                    :    5
%              Number of atoms          :   78 ( 142 expanded)
%              Number of equality atoms :   45 ( 103 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_32,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_358,plain,(
    ! [A_107,B_108] : k1_enumset1(A_107,A_107,B_108) = k2_tarski(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [E_11,A_5,C_7] : r2_hidden(E_11,k1_enumset1(A_5,E_11,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_376,plain,(
    ! [A_109,B_110] : r2_hidden(A_109,k2_tarski(A_109,B_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_12])).

tff(c_379,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_376])).

tff(c_220,plain,(
    ! [A_75,B_76] : k1_enumset1(A_75,A_75,B_76) = k2_tarski(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_238,plain,(
    ! [B_77,A_78] : r2_hidden(B_77,k2_tarski(A_78,B_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_10])).

tff(c_241,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_238])).

tff(c_46,plain,
    ( '#skF_3' != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_51,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_77,plain,(
    ! [A_42,B_43] :
      ( r1_xboole_0(k1_tarski(A_42),B_43)
      | r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(k1_tarski(A_58),B_59) = k1_tarski(A_58)
      | r2_hidden(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_77,c_4])).

tff(c_44,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_149,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_76])).

tff(c_34,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_160,plain,(
    ! [E_64,C_65,B_66,A_67] :
      ( E_64 = C_65
      | E_64 = B_66
      | E_64 = A_67
      | ~ r2_hidden(E_64,k1_enumset1(A_67,B_66,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_179,plain,(
    ! [E_68,B_69,A_70] :
      ( E_68 = B_69
      | E_68 = A_70
      | E_68 = A_70
      | ~ r2_hidden(E_68,k2_tarski(A_70,B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_160])).

tff(c_193,plain,(
    ! [E_71,A_72] :
      ( E_71 = A_72
      | E_71 = A_72
      | E_71 = A_72
      | ~ r2_hidden(E_71,k1_tarski(A_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_179])).

tff(c_196,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_149,c_193])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_51,c_51,c_196])).

tff(c_204,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_205,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_272,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_204,c_205,c_48])).

tff(c_66,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k4_xboole_0(A_40,B_41) != A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden(A_22,B_23)
      | ~ r1_xboole_0(k1_tarski(A_22),B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_304,plain,(
    ! [A_89,B_90] :
      ( ~ r2_hidden(A_89,B_90)
      | k4_xboole_0(k1_tarski(A_89),B_90) != k1_tarski(A_89) ) ),
    inference(resolution,[status(thm)],[c_66,c_40])).

tff(c_310,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_304])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_310])).

tff(c_319,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_320,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( '#skF_3' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_343,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_319,c_320,c_50])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_381,plain,(
    ! [A_112,B_113] :
      ( ~ r2_hidden(A_112,B_113)
      | ~ r1_xboole_0(k1_tarski(A_112),B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_435,plain,(
    ! [A_123,B_124] :
      ( ~ r2_hidden(A_123,B_124)
      | k4_xboole_0(k1_tarski(A_123),B_124) != k1_tarski(A_123) ) ),
    inference(resolution,[status(thm)],[c_6,c_381])).

tff(c_441,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_435])).

tff(c_446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:37:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.90  
% 2.59/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.90  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.59/1.90  
% 2.59/1.90  %Foreground sorts:
% 2.59/1.90  
% 2.59/1.90  
% 2.59/1.90  %Background operators:
% 2.59/1.90  
% 2.59/1.90  
% 2.59/1.90  %Foreground operators:
% 2.59/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.59/1.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.59/1.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.59/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.90  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.59/1.90  tff('#skF_6', type, '#skF_6': $i).
% 2.59/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.59/1.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.90  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.90  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.90  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.59/1.90  
% 2.80/1.95  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.80/1.95  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.80/1.95  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.80/1.95  tff(f_70, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.80/1.95  tff(f_64, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.80/1.95  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.80/1.95  tff(f_59, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.80/1.95  tff(c_32, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.95  tff(c_358, plain, (![A_107, B_108]: (k1_enumset1(A_107, A_107, B_108)=k2_tarski(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.80/1.95  tff(c_12, plain, (![E_11, A_5, C_7]: (r2_hidden(E_11, k1_enumset1(A_5, E_11, C_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.80/1.95  tff(c_376, plain, (![A_109, B_110]: (r2_hidden(A_109, k2_tarski(A_109, B_110)))), inference(superposition, [status(thm), theory('equality')], [c_358, c_12])).
% 2.80/1.95  tff(c_379, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_376])).
% 2.80/1.95  tff(c_220, plain, (![A_75, B_76]: (k1_enumset1(A_75, A_75, B_76)=k2_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.80/1.95  tff(c_10, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.80/1.95  tff(c_238, plain, (![B_77, A_78]: (r2_hidden(B_77, k2_tarski(A_78, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_220, c_10])).
% 2.80/1.95  tff(c_241, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_238])).
% 2.80/1.95  tff(c_46, plain, ('#skF_3'!='#skF_4' | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.95  tff(c_51, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_46])).
% 2.80/1.95  tff(c_77, plain, (![A_42, B_43]: (r1_xboole_0(k1_tarski(A_42), B_43) | r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.80/1.95  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.95  tff(c_134, plain, (![A_58, B_59]: (k4_xboole_0(k1_tarski(A_58), B_59)=k1_tarski(A_58) | r2_hidden(A_58, B_59))), inference(resolution, [status(thm)], [c_77, c_4])).
% 2.80/1.95  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.95  tff(c_76, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 2.80/1.95  tff(c_149, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_76])).
% 2.80/1.95  tff(c_34, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.80/1.95  tff(c_160, plain, (![E_64, C_65, B_66, A_67]: (E_64=C_65 | E_64=B_66 | E_64=A_67 | ~r2_hidden(E_64, k1_enumset1(A_67, B_66, C_65)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.80/1.95  tff(c_179, plain, (![E_68, B_69, A_70]: (E_68=B_69 | E_68=A_70 | E_68=A_70 | ~r2_hidden(E_68, k2_tarski(A_70, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_160])).
% 2.80/1.95  tff(c_193, plain, (![E_71, A_72]: (E_71=A_72 | E_71=A_72 | E_71=A_72 | ~r2_hidden(E_71, k1_tarski(A_72)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_179])).
% 2.80/1.95  tff(c_196, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_149, c_193])).
% 2.80/1.95  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_51, c_51, c_196])).
% 2.80/1.95  tff(c_204, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 2.80/1.95  tff(c_205, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 2.80/1.95  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.95  tff(c_272, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_204, c_205, c_48])).
% 2.80/1.95  tff(c_66, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k4_xboole_0(A_40, B_41)!=A_40)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.95  tff(c_40, plain, (![A_22, B_23]: (~r2_hidden(A_22, B_23) | ~r1_xboole_0(k1_tarski(A_22), B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.95  tff(c_304, plain, (![A_89, B_90]: (~r2_hidden(A_89, B_90) | k4_xboole_0(k1_tarski(A_89), B_90)!=k1_tarski(A_89))), inference(resolution, [status(thm)], [c_66, c_40])).
% 2.80/1.95  tff(c_310, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_272, c_304])).
% 2.80/1.95  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_241, c_310])).
% 2.80/1.95  tff(c_319, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 2.80/1.95  tff(c_320, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.80/1.95  tff(c_50, plain, ('#skF_3'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.95  tff(c_343, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_319, c_320, c_50])).
% 2.80/1.95  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k4_xboole_0(A_3, B_4)!=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.95  tff(c_381, plain, (![A_112, B_113]: (~r2_hidden(A_112, B_113) | ~r1_xboole_0(k1_tarski(A_112), B_113))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.95  tff(c_435, plain, (![A_123, B_124]: (~r2_hidden(A_123, B_124) | k4_xboole_0(k1_tarski(A_123), B_124)!=k1_tarski(A_123))), inference(resolution, [status(thm)], [c_6, c_381])).
% 2.80/1.95  tff(c_441, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_343, c_435])).
% 2.80/1.95  tff(c_446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_379, c_441])).
% 2.80/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.95  
% 2.80/1.95  Inference rules
% 2.80/1.95  ----------------------
% 2.80/1.95  #Ref     : 0
% 2.80/1.95  #Sup     : 89
% 2.80/1.95  #Fact    : 0
% 2.80/1.95  #Define  : 0
% 2.80/1.95  #Split   : 2
% 2.80/1.95  #Chain   : 0
% 2.80/1.95  #Close   : 0
% 2.80/1.95  
% 2.80/1.95  Ordering : KBO
% 2.80/1.95  
% 2.80/1.95  Simplification rules
% 2.80/1.95  ----------------------
% 2.80/1.95  #Subsume      : 3
% 2.80/1.95  #Demod        : 23
% 2.80/1.95  #Tautology    : 68
% 2.80/1.95  #SimpNegUnit  : 1
% 2.80/1.95  #BackRed      : 0
% 2.80/1.95  
% 2.80/1.95  #Partial instantiations: 0
% 2.80/1.95  #Strategies tried      : 1
% 2.80/1.95  
% 2.80/1.95  Timing (in seconds)
% 2.80/1.95  ----------------------
% 2.80/1.96  Preprocessing        : 0.55
% 2.80/1.96  Parsing              : 0.30
% 2.80/1.96  CNF conversion       : 0.04
% 2.80/1.96  Main loop            : 0.42
% 2.80/1.96  Inferencing          : 0.18
% 2.80/1.96  Reduction            : 0.11
% 2.80/1.96  Demodulation         : 0.08
% 2.80/1.96  BG Simplification    : 0.02
% 2.80/1.96  Subsumption          : 0.07
% 2.80/1.96  Abstraction          : 0.02
% 2.80/1.96  MUC search           : 0.00
% 2.80/1.97  Cooper               : 0.00
% 2.80/1.97  Total                : 1.05
% 2.80/1.97  Index Insertion      : 0.00
% 2.80/1.97  Index Deletion       : 0.00
% 2.80/1.97  Index Matching       : 0.00
% 2.80/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
