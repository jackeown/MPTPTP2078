%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:11 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   60 (  87 expanded)
%              Number of leaves         :   27 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 130 expanded)
%              Number of equality atoms :   49 (  92 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_84,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_46,plain,(
    ! [A_22] : k2_zfmisc_1(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_103,plain,(
    ! [A_46,B_47] : ~ r2_hidden(A_46,k2_zfmisc_1(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_106,plain,(
    ! [A_22] : ~ r2_hidden(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_103])).

tff(c_66,plain,(
    k4_tarski('#skF_7','#skF_8') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_432,plain,(
    ! [A_107,B_108] : k2_mcart_1(k4_tarski(A_107,B_108)) = B_108 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_441,plain,(
    k2_mcart_1('#skF_6') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_432])).

tff(c_64,plain,
    ( k2_mcart_1('#skF_6') = '#skF_6'
    | k1_mcart_1('#skF_6') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_116,plain,(
    k1_mcart_1('#skF_6') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_142,plain,(
    ! [A_55,B_56] : k1_mcart_1(k4_tarski(A_55,B_56)) = A_55 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_151,plain,(
    k1_mcart_1('#skF_6') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_142])).

tff(c_154,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_151])).

tff(c_162,plain,(
    k4_tarski('#skF_6','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_66])).

tff(c_58,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_5'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_179,plain,(
    ! [C_58,A_59] :
      ( C_58 = A_59
      | ~ r2_hidden(C_58,k1_tarski(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_187,plain,(
    ! [A_59] :
      ( '#skF_5'(k1_tarski(A_59)) = A_59
      | k1_tarski(A_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58,c_179])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_327,plain,(
    ! [C_89,A_90,D_91] :
      ( ~ r2_hidden(C_89,A_90)
      | k4_tarski(C_89,D_91) != '#skF_5'(A_90)
      | k1_xboole_0 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_344,plain,(
    ! [C_94,D_95] :
      ( k4_tarski(C_94,D_95) != '#skF_5'(k1_tarski(C_94))
      | k1_tarski(C_94) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_327])).

tff(c_369,plain,(
    ! [A_103,D_104] :
      ( k4_tarski(A_103,D_104) != A_103
      | k1_tarski(A_103) = k1_xboole_0
      | k1_tarski(A_103) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_344])).

tff(c_373,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_369])).

tff(c_399,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_4])).

tff(c_408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_399])).

tff(c_409,plain,(
    k2_mcart_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_444,plain,(
    '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_409])).

tff(c_452,plain,(
    k4_tarski('#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_66])).

tff(c_489,plain,(
    ! [C_112,A_113] :
      ( C_112 = A_113
      | ~ r2_hidden(C_112,k1_tarski(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_497,plain,(
    ! [A_113] :
      ( '#skF_5'(k1_tarski(A_113)) = A_113
      | k1_tarski(A_113) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58,c_489])).

tff(c_606,plain,(
    ! [D_135,A_136,C_137] :
      ( ~ r2_hidden(D_135,A_136)
      | k4_tarski(C_137,D_135) != '#skF_5'(A_136)
      | k1_xboole_0 = A_136 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_629,plain,(
    ! [C_142,C_143] :
      ( k4_tarski(C_142,C_143) != '#skF_5'(k1_tarski(C_143))
      | k1_tarski(C_143) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_606])).

tff(c_680,plain,(
    ! [C_159,A_160] :
      ( k4_tarski(C_159,A_160) != A_160
      | k1_tarski(A_160) = k1_xboole_0
      | k1_tarski(A_160) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_629])).

tff(c_684,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_680])).

tff(c_710,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_4])).

tff(c_719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.56  
% 2.81/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.56  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 2.81/1.56  
% 2.81/1.56  %Foreground sorts:
% 2.81/1.56  
% 2.81/1.56  
% 2.81/1.56  %Background operators:
% 2.81/1.56  
% 2.81/1.56  
% 2.81/1.56  %Foreground operators:
% 2.81/1.56  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.81/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.81/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.81/1.56  tff('#skF_7', type, '#skF_7': $i).
% 2.81/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.56  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.56  tff('#skF_8', type, '#skF_8': $i).
% 2.81/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.56  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.81/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.81/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.56  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.81/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.56  
% 2.81/1.57  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.81/1.57  tff(f_62, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.81/1.57  tff(f_94, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.81/1.57  tff(f_68, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.81/1.57  tff(f_84, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.81/1.57  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.81/1.57  tff(c_46, plain, (![A_22]: (k2_zfmisc_1(A_22, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.81/1.57  tff(c_103, plain, (![A_46, B_47]: (~r2_hidden(A_46, k2_zfmisc_1(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.81/1.57  tff(c_106, plain, (![A_22]: (~r2_hidden(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_103])).
% 2.81/1.57  tff(c_66, plain, (k4_tarski('#skF_7', '#skF_8')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.81/1.57  tff(c_432, plain, (![A_107, B_108]: (k2_mcart_1(k4_tarski(A_107, B_108))=B_108)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.81/1.57  tff(c_441, plain, (k2_mcart_1('#skF_6')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_66, c_432])).
% 2.81/1.57  tff(c_64, plain, (k2_mcart_1('#skF_6')='#skF_6' | k1_mcart_1('#skF_6')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.81/1.57  tff(c_116, plain, (k1_mcart_1('#skF_6')='#skF_6'), inference(splitLeft, [status(thm)], [c_64])).
% 2.81/1.57  tff(c_142, plain, (![A_55, B_56]: (k1_mcart_1(k4_tarski(A_55, B_56))=A_55)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.81/1.57  tff(c_151, plain, (k1_mcart_1('#skF_6')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_66, c_142])).
% 2.81/1.57  tff(c_154, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_151])).
% 2.81/1.57  tff(c_162, plain, (k4_tarski('#skF_6', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_66])).
% 2.81/1.57  tff(c_58, plain, (![A_30]: (r2_hidden('#skF_5'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.81/1.57  tff(c_179, plain, (![C_58, A_59]: (C_58=A_59 | ~r2_hidden(C_58, k1_tarski(A_59)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.57  tff(c_187, plain, (![A_59]: ('#skF_5'(k1_tarski(A_59))=A_59 | k1_tarski(A_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_179])).
% 2.81/1.57  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.57  tff(c_327, plain, (![C_89, A_90, D_91]: (~r2_hidden(C_89, A_90) | k4_tarski(C_89, D_91)!='#skF_5'(A_90) | k1_xboole_0=A_90)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.81/1.57  tff(c_344, plain, (![C_94, D_95]: (k4_tarski(C_94, D_95)!='#skF_5'(k1_tarski(C_94)) | k1_tarski(C_94)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_327])).
% 2.81/1.57  tff(c_369, plain, (![A_103, D_104]: (k4_tarski(A_103, D_104)!=A_103 | k1_tarski(A_103)=k1_xboole_0 | k1_tarski(A_103)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_187, c_344])).
% 2.81/1.57  tff(c_373, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_162, c_369])).
% 2.81/1.57  tff(c_399, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_373, c_4])).
% 2.81/1.57  tff(c_408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_399])).
% 2.81/1.57  tff(c_409, plain, (k2_mcart_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_64])).
% 2.81/1.57  tff(c_444, plain, ('#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_441, c_409])).
% 2.81/1.57  tff(c_452, plain, (k4_tarski('#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_444, c_66])).
% 2.81/1.57  tff(c_489, plain, (![C_112, A_113]: (C_112=A_113 | ~r2_hidden(C_112, k1_tarski(A_113)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.57  tff(c_497, plain, (![A_113]: ('#skF_5'(k1_tarski(A_113))=A_113 | k1_tarski(A_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_489])).
% 2.81/1.57  tff(c_606, plain, (![D_135, A_136, C_137]: (~r2_hidden(D_135, A_136) | k4_tarski(C_137, D_135)!='#skF_5'(A_136) | k1_xboole_0=A_136)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.81/1.57  tff(c_629, plain, (![C_142, C_143]: (k4_tarski(C_142, C_143)!='#skF_5'(k1_tarski(C_143)) | k1_tarski(C_143)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_606])).
% 2.81/1.57  tff(c_680, plain, (![C_159, A_160]: (k4_tarski(C_159, A_160)!=A_160 | k1_tarski(A_160)=k1_xboole_0 | k1_tarski(A_160)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_497, c_629])).
% 2.81/1.57  tff(c_684, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_452, c_680])).
% 2.81/1.57  tff(c_710, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_684, c_4])).
% 2.81/1.57  tff(c_719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_710])).
% 2.81/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.57  
% 2.81/1.57  Inference rules
% 2.81/1.57  ----------------------
% 2.81/1.57  #Ref     : 0
% 2.81/1.57  #Sup     : 171
% 2.81/1.57  #Fact    : 0
% 2.81/1.57  #Define  : 0
% 2.81/1.57  #Split   : 1
% 2.81/1.57  #Chain   : 0
% 2.81/1.57  #Close   : 0
% 2.81/1.57  
% 2.81/1.58  Ordering : KBO
% 2.81/1.58  
% 2.81/1.58  Simplification rules
% 2.81/1.58  ----------------------
% 2.81/1.58  #Subsume      : 23
% 2.81/1.58  #Demod        : 34
% 2.81/1.58  #Tautology    : 87
% 2.81/1.58  #SimpNegUnit  : 10
% 2.81/1.58  #BackRed      : 9
% 2.81/1.58  
% 2.81/1.58  #Partial instantiations: 0
% 2.81/1.58  #Strategies tried      : 1
% 2.81/1.58  
% 2.81/1.58  Timing (in seconds)
% 2.81/1.58  ----------------------
% 2.81/1.58  Preprocessing        : 0.40
% 2.81/1.58  Parsing              : 0.19
% 2.81/1.58  CNF conversion       : 0.03
% 2.81/1.58  Main loop            : 0.31
% 2.81/1.58  Inferencing          : 0.11
% 2.81/1.58  Reduction            : 0.10
% 2.81/1.58  Demodulation         : 0.07
% 2.81/1.58  BG Simplification    : 0.02
% 2.81/1.58  Subsumption          : 0.05
% 2.81/1.58  Abstraction          : 0.02
% 2.81/1.58  MUC search           : 0.00
% 2.81/1.58  Cooper               : 0.00
% 2.81/1.58  Total                : 0.75
% 2.81/1.58  Index Insertion      : 0.00
% 2.81/1.58  Index Deletion       : 0.00
% 2.81/1.58  Index Matching       : 0.00
% 2.81/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
