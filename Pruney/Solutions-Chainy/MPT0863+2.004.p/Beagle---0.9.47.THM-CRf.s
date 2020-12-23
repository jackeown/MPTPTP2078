%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:07 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   53 (  89 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :    4
%              Number of atoms          :   74 ( 186 expanded)
%              Number of equality atoms :   50 ( 138 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k2_tarski(D,E)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & ( k2_mcart_1(A) = D
            | k2_mcart_1(A) = E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_42,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_43,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    k2_mcart_1('#skF_3') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_69,plain,(
    ! [A_31,C_32,B_33] :
      ( r2_hidden(k2_mcart_1(A_31),C_32)
      | ~ r2_hidden(A_31,k2_zfmisc_1(B_33,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_69])).

tff(c_26,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_86,plain,(
    ! [E_40,C_41,B_42,A_43] :
      ( E_40 = C_41
      | E_40 = B_42
      | E_40 = A_43
      | ~ r2_hidden(E_40,k1_enumset1(A_43,B_42,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_105,plain,(
    ! [E_44,B_45,A_46] :
      ( E_44 = B_45
      | E_44 = A_46
      | E_44 = A_46
      | ~ r2_hidden(E_44,k2_tarski(A_46,B_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_86])).

tff(c_111,plain,
    ( k2_mcart_1('#skF_3') = '#skF_7'
    | k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_72,c_105])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_43,c_46,c_111])).

tff(c_124,plain,(
    k2_mcart_1('#skF_3') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_131,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_38])).

tff(c_123,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_154,plain,(
    ! [A_56,B_57,C_58] :
      ( r2_hidden(k1_mcart_1(A_56),B_57)
      | ~ r2_hidden(A_56,k2_zfmisc_1(B_57,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_157,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_154])).

tff(c_172,plain,(
    ! [E_65,C_66,B_67,A_68] :
      ( E_65 = C_66
      | E_65 = B_67
      | E_65 = A_68
      | ~ r2_hidden(E_65,k1_enumset1(A_68,B_67,C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_191,plain,(
    ! [E_69,B_70,A_71] :
      ( E_69 = B_70
      | E_69 = A_71
      | E_69 = A_71
      | ~ r2_hidden(E_69,k2_tarski(A_71,B_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_172])).

tff(c_194,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_157,c_191])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_131,c_123,c_194])).

tff(c_205,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_206,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_212,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_40])).

tff(c_244,plain,(
    ! [A_90,B_91,C_92] :
      ( r2_hidden(k1_mcart_1(A_90),B_91)
      | ~ r2_hidden(A_90,k2_zfmisc_1(B_91,C_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_247,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_244])).

tff(c_257,plain,(
    ! [E_96,C_97,B_98,A_99] :
      ( E_96 = C_97
      | E_96 = B_98
      | E_96 = A_99
      | ~ r2_hidden(E_96,k1_enumset1(A_99,B_98,C_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_277,plain,(
    ! [E_104,B_105,A_106] :
      ( E_104 = B_105
      | E_104 = A_106
      | E_104 = A_106
      | ~ r2_hidden(E_104,k2_tarski(A_106,B_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_257])).

tff(c_280,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_247,c_277])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_205,c_212,c_280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:03:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.31  
% 2.03/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.32  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.03/1.32  
% 2.03/1.32  %Foreground sorts:
% 2.03/1.32  
% 2.03/1.32  
% 2.03/1.32  %Background operators:
% 2.03/1.32  
% 2.03/1.32  
% 2.03/1.32  %Foreground operators:
% 2.03/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.03/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.03/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.03/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.32  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.03/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.32  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.03/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.03/1.32  
% 2.03/1.33  tff(f_61, negated_conjecture, ~(![A, B, C, D, E]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k2_tarski(D, E))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & ((k2_mcart_1(A) = D) | (k2_mcart_1(A) = E))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_mcart_1)).
% 2.03/1.33  tff(f_50, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.03/1.33  tff(f_42, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.03/1.33  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.03/1.33  tff(c_42, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.33  tff(c_43, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_42])).
% 2.03/1.33  tff(c_36, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.33  tff(c_46, plain, (k2_mcart_1('#skF_3')!='#skF_7'), inference(splitLeft, [status(thm)], [c_36])).
% 2.03/1.33  tff(c_34, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.33  tff(c_69, plain, (![A_31, C_32, B_33]: (r2_hidden(k2_mcart_1(A_31), C_32) | ~r2_hidden(A_31, k2_zfmisc_1(B_33, C_32)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.03/1.33  tff(c_72, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_69])).
% 2.03/1.33  tff(c_26, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.03/1.33  tff(c_86, plain, (![E_40, C_41, B_42, A_43]: (E_40=C_41 | E_40=B_42 | E_40=A_43 | ~r2_hidden(E_40, k1_enumset1(A_43, B_42, C_41)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.33  tff(c_105, plain, (![E_44, B_45, A_46]: (E_44=B_45 | E_44=A_46 | E_44=A_46 | ~r2_hidden(E_44, k2_tarski(A_46, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_86])).
% 2.03/1.33  tff(c_111, plain, (k2_mcart_1('#skF_3')='#skF_7' | k2_mcart_1('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_72, c_105])).
% 2.03/1.33  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_43, c_46, c_111])).
% 2.03/1.33  tff(c_124, plain, (k2_mcart_1('#skF_3')='#skF_7'), inference(splitRight, [status(thm)], [c_36])).
% 2.03/1.33  tff(c_38, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.33  tff(c_131, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_38])).
% 2.03/1.33  tff(c_123, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 2.03/1.33  tff(c_154, plain, (![A_56, B_57, C_58]: (r2_hidden(k1_mcart_1(A_56), B_57) | ~r2_hidden(A_56, k2_zfmisc_1(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.03/1.33  tff(c_157, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_154])).
% 2.03/1.33  tff(c_172, plain, (![E_65, C_66, B_67, A_68]: (E_65=C_66 | E_65=B_67 | E_65=A_68 | ~r2_hidden(E_65, k1_enumset1(A_68, B_67, C_66)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.33  tff(c_191, plain, (![E_69, B_70, A_71]: (E_69=B_70 | E_69=A_71 | E_69=A_71 | ~r2_hidden(E_69, k2_tarski(A_71, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_172])).
% 2.03/1.33  tff(c_194, plain, (k1_mcart_1('#skF_3')='#skF_5' | k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_157, c_191])).
% 2.03/1.33  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_131, c_123, c_194])).
% 2.03/1.33  tff(c_205, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 2.03/1.33  tff(c_206, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 2.03/1.33  tff(c_40, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.33  tff(c_212, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_206, c_40])).
% 2.03/1.33  tff(c_244, plain, (![A_90, B_91, C_92]: (r2_hidden(k1_mcart_1(A_90), B_91) | ~r2_hidden(A_90, k2_zfmisc_1(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.03/1.33  tff(c_247, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_244])).
% 2.03/1.33  tff(c_257, plain, (![E_96, C_97, B_98, A_99]: (E_96=C_97 | E_96=B_98 | E_96=A_99 | ~r2_hidden(E_96, k1_enumset1(A_99, B_98, C_97)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.33  tff(c_277, plain, (![E_104, B_105, A_106]: (E_104=B_105 | E_104=A_106 | E_104=A_106 | ~r2_hidden(E_104, k2_tarski(A_106, B_105)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_257])).
% 2.03/1.33  tff(c_280, plain, (k1_mcart_1('#skF_3')='#skF_5' | k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_247, c_277])).
% 2.03/1.33  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_205, c_212, c_280])).
% 2.03/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.33  
% 2.03/1.33  Inference rules
% 2.03/1.33  ----------------------
% 2.03/1.33  #Ref     : 0
% 2.03/1.33  #Sup     : 53
% 2.03/1.33  #Fact    : 0
% 2.03/1.33  #Define  : 0
% 2.03/1.33  #Split   : 2
% 2.03/1.33  #Chain   : 0
% 2.03/1.33  #Close   : 0
% 2.03/1.33  
% 2.03/1.33  Ordering : KBO
% 2.03/1.33  
% 2.03/1.33  Simplification rules
% 2.03/1.33  ----------------------
% 2.03/1.33  #Subsume      : 4
% 2.03/1.33  #Demod        : 12
% 2.03/1.33  #Tautology    : 30
% 2.03/1.33  #SimpNegUnit  : 3
% 2.03/1.33  #BackRed      : 1
% 2.03/1.33  
% 2.03/1.33  #Partial instantiations: 0
% 2.03/1.33  #Strategies tried      : 1
% 2.03/1.33  
% 2.03/1.33  Timing (in seconds)
% 2.03/1.33  ----------------------
% 2.03/1.33  Preprocessing        : 0.31
% 2.03/1.33  Parsing              : 0.16
% 2.03/1.33  CNF conversion       : 0.02
% 2.03/1.33  Main loop            : 0.20
% 2.03/1.33  Inferencing          : 0.08
% 2.03/1.33  Reduction            : 0.06
% 2.03/1.33  Demodulation         : 0.04
% 2.03/1.33  BG Simplification    : 0.01
% 2.03/1.33  Subsumption          : 0.03
% 2.03/1.33  Abstraction          : 0.01
% 2.03/1.33  MUC search           : 0.00
% 2.03/1.33  Cooper               : 0.00
% 2.03/1.33  Total                : 0.53
% 2.03/1.33  Index Insertion      : 0.00
% 2.03/1.33  Index Deletion       : 0.00
% 2.03/1.33  Index Matching       : 0.00
% 2.03/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
