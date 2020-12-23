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
% DateTime   : Thu Dec  3 10:09:08 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 126 expanded)
%              Number of leaves         :   27 (  57 expanded)
%              Depth                    :    6
%              Number of atoms          :   94 ( 269 expanded)
%              Number of equality atoms :   49 ( 161 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k2_tarski(D,E)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & ( k2_mcart_1(A) = D
            | k2_mcart_1(A) = E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_48,plain,
    ( k1_mcart_1('#skF_7') != '#skF_9'
    | k2_mcart_1('#skF_7') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_69,plain,(
    k2_mcart_1('#skF_7') != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,
    ( k1_mcart_1('#skF_7') != '#skF_9'
    | k2_mcart_1('#skF_7') != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,(
    k2_mcart_1('#skF_7') != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    r2_hidden('#skF_7',k2_zfmisc_1(k2_tarski('#skF_8','#skF_9'),k2_tarski('#skF_10','#skF_11'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_106,plain,(
    ! [A_68,D_69,C_70,B_71] :
      ( k2_mcart_1(A_68) = D_69
      | k2_mcart_1(A_68) = C_70
      | ~ r2_hidden(A_68,k2_zfmisc_1(B_71,k2_tarski(C_70,D_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_113,plain,
    ( k2_mcart_1('#skF_7') = '#skF_11'
    | k2_mcart_1('#skF_7') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_42,c_106])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_70,c_113])).

tff(c_121,plain,(
    k2_mcart_1('#skF_7') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( k1_mcart_1('#skF_7') != '#skF_8'
    | k2_mcart_1('#skF_7') != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_128,plain,(
    k1_mcart_1('#skF_7') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_46])).

tff(c_120,plain,(
    k1_mcart_1('#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_32,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(k1_mcart_1(A_40),B_41)
      | ~ r2_hidden(A_40,k2_zfmisc_1(B_41,C_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_156,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_tarski('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_42,c_32])).

tff(c_40,plain,(
    ! [A_47,B_48] : k2_mcart_1(k4_tarski(A_47,B_48)) = B_48 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_164,plain,(
    ! [E_87,F_88,A_89,B_90] :
      ( r2_hidden(k4_tarski(E_87,F_88),k2_zfmisc_1(A_89,B_90))
      | ~ r2_hidden(F_88,B_90)
      | ~ r2_hidden(E_87,A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [A_43,D_46,C_45,B_44] :
      ( k2_mcart_1(A_43) = D_46
      | k2_mcart_1(A_43) = C_45
      | ~ r2_hidden(A_43,k2_zfmisc_1(B_44,k2_tarski(C_45,D_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_168,plain,(
    ! [E_87,F_88,A_89,D_46,C_45] :
      ( k2_mcart_1(k4_tarski(E_87,F_88)) = D_46
      | k2_mcart_1(k4_tarski(E_87,F_88)) = C_45
      | ~ r2_hidden(F_88,k2_tarski(C_45,D_46))
      | ~ r2_hidden(E_87,A_89) ) ),
    inference(resolution,[status(thm)],[c_164,c_34])).

tff(c_174,plain,(
    ! [E_87,F_88,A_89,D_46,C_45] :
      ( F_88 = D_46
      | F_88 = C_45
      | ~ r2_hidden(F_88,k2_tarski(C_45,D_46))
      | ~ r2_hidden(E_87,A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_168])).

tff(c_179,plain,(
    ! [E_87,A_89] : ~ r2_hidden(E_87,A_89) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_156])).

tff(c_188,plain,(
    ! [F_91,D_92,C_93] :
      ( F_91 = D_92
      | F_91 = C_93
      | ~ r2_hidden(F_91,k2_tarski(C_93,D_92)) ) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_191,plain,
    ( k1_mcart_1('#skF_7') = '#skF_9'
    | k1_mcart_1('#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_156,c_188])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_120,c_191])).

tff(c_200,plain,(
    k2_mcart_1('#skF_7') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( k1_mcart_1('#skF_7') != '#skF_8'
    | k2_mcart_1('#skF_7') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_206,plain,(
    k1_mcart_1('#skF_7') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_50])).

tff(c_199,plain,(
    k1_mcart_1('#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_218,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden(k1_mcart_1(A_96),B_97)
      | ~ r2_hidden(A_96,k2_zfmisc_1(B_97,C_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_221,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_tarski('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_42,c_218])).

tff(c_242,plain,(
    ! [E_109,F_110,A_111,B_112] :
      ( r2_hidden(k4_tarski(E_109,F_110),k2_zfmisc_1(A_111,B_112))
      | ~ r2_hidden(F_110,B_112)
      | ~ r2_hidden(E_109,A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_246,plain,(
    ! [A_111,F_110,D_46,E_109,C_45] :
      ( k2_mcart_1(k4_tarski(E_109,F_110)) = D_46
      | k2_mcart_1(k4_tarski(E_109,F_110)) = C_45
      | ~ r2_hidden(F_110,k2_tarski(C_45,D_46))
      | ~ r2_hidden(E_109,A_111) ) ),
    inference(resolution,[status(thm)],[c_242,c_34])).

tff(c_252,plain,(
    ! [A_111,F_110,D_46,E_109,C_45] :
      ( F_110 = D_46
      | F_110 = C_45
      | ~ r2_hidden(F_110,k2_tarski(C_45,D_46))
      | ~ r2_hidden(E_109,A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_246])).

tff(c_257,plain,(
    ! [E_109,A_111] : ~ r2_hidden(E_109,A_111) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_231,plain,(
    ! [A_102,C_103,B_104] :
      ( r2_hidden(k2_mcart_1(A_102),C_103)
      | ~ r2_hidden(A_102,k2_zfmisc_1(B_104,C_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_233,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),k2_tarski('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_42,c_231])).

tff(c_235,plain,(
    r2_hidden('#skF_10',k2_tarski('#skF_10','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_233])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_235])).

tff(c_281,plain,(
    ! [F_116,D_117,C_118] :
      ( F_116 = D_117
      | F_116 = C_118
      | ~ r2_hidden(F_116,k2_tarski(C_118,D_117)) ) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_287,plain,
    ( k1_mcart_1('#skF_7') = '#skF_9'
    | k1_mcart_1('#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_221,c_281])).

tff(c_293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_199,c_287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.61  
% 2.54/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.61  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 2.54/1.61  
% 2.54/1.61  %Foreground sorts:
% 2.54/1.61  
% 2.54/1.61  
% 2.54/1.61  %Background operators:
% 2.54/1.61  
% 2.54/1.61  
% 2.54/1.61  %Foreground operators:
% 2.54/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.54/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.61  tff('#skF_11', type, '#skF_11': $i).
% 2.54/1.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.54/1.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.54/1.61  tff('#skF_7', type, '#skF_7': $i).
% 2.54/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.61  tff('#skF_10', type, '#skF_10': $i).
% 2.54/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.54/1.61  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.54/1.61  tff('#skF_9', type, '#skF_9': $i).
% 2.54/1.61  tff('#skF_8', type, '#skF_8': $i).
% 2.54/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.61  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.54/1.61  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.54/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.54/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.61  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.54/1.61  
% 2.54/1.64  tff(f_70, negated_conjecture, ~(![A, B, C, D, E]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k2_tarski(D, E))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & ((k2_mcart_1(A) = D) | (k2_mcart_1(A) = E))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_mcart_1)).
% 2.54/1.64  tff(f_55, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 2.54/1.64  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.54/1.64  tff(f_59, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.54/1.64  tff(f_41, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.54/1.64  tff(c_48, plain, (k1_mcart_1('#skF_7')!='#skF_9' | k2_mcart_1('#skF_7')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.64  tff(c_69, plain, (k2_mcart_1('#skF_7')!='#skF_10'), inference(splitLeft, [status(thm)], [c_48])).
% 2.54/1.64  tff(c_44, plain, (k1_mcart_1('#skF_7')!='#skF_9' | k2_mcart_1('#skF_7')!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.64  tff(c_70, plain, (k2_mcart_1('#skF_7')!='#skF_11'), inference(splitLeft, [status(thm)], [c_44])).
% 2.54/1.64  tff(c_42, plain, (r2_hidden('#skF_7', k2_zfmisc_1(k2_tarski('#skF_8', '#skF_9'), k2_tarski('#skF_10', '#skF_11')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.64  tff(c_106, plain, (![A_68, D_69, C_70, B_71]: (k2_mcart_1(A_68)=D_69 | k2_mcart_1(A_68)=C_70 | ~r2_hidden(A_68, k2_zfmisc_1(B_71, k2_tarski(C_70, D_69))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.54/1.64  tff(c_113, plain, (k2_mcart_1('#skF_7')='#skF_11' | k2_mcart_1('#skF_7')='#skF_10'), inference(resolution, [status(thm)], [c_42, c_106])).
% 2.54/1.64  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_70, c_113])).
% 2.54/1.64  tff(c_121, plain, (k2_mcart_1('#skF_7')='#skF_11'), inference(splitRight, [status(thm)], [c_44])).
% 2.54/1.64  tff(c_46, plain, (k1_mcart_1('#skF_7')!='#skF_8' | k2_mcart_1('#skF_7')!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.64  tff(c_128, plain, (k1_mcart_1('#skF_7')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_46])).
% 2.54/1.64  tff(c_120, plain, (k1_mcart_1('#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_44])).
% 2.54/1.64  tff(c_32, plain, (![A_40, B_41, C_42]: (r2_hidden(k1_mcart_1(A_40), B_41) | ~r2_hidden(A_40, k2_zfmisc_1(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.54/1.64  tff(c_156, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_tarski('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_42, c_32])).
% 2.54/1.64  tff(c_40, plain, (![A_47, B_48]: (k2_mcart_1(k4_tarski(A_47, B_48))=B_48)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.54/1.64  tff(c_164, plain, (![E_87, F_88, A_89, B_90]: (r2_hidden(k4_tarski(E_87, F_88), k2_zfmisc_1(A_89, B_90)) | ~r2_hidden(F_88, B_90) | ~r2_hidden(E_87, A_89))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.54/1.64  tff(c_34, plain, (![A_43, D_46, C_45, B_44]: (k2_mcart_1(A_43)=D_46 | k2_mcart_1(A_43)=C_45 | ~r2_hidden(A_43, k2_zfmisc_1(B_44, k2_tarski(C_45, D_46))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.54/1.64  tff(c_168, plain, (![E_87, F_88, A_89, D_46, C_45]: (k2_mcart_1(k4_tarski(E_87, F_88))=D_46 | k2_mcart_1(k4_tarski(E_87, F_88))=C_45 | ~r2_hidden(F_88, k2_tarski(C_45, D_46)) | ~r2_hidden(E_87, A_89))), inference(resolution, [status(thm)], [c_164, c_34])).
% 2.54/1.64  tff(c_174, plain, (![E_87, F_88, A_89, D_46, C_45]: (F_88=D_46 | F_88=C_45 | ~r2_hidden(F_88, k2_tarski(C_45, D_46)) | ~r2_hidden(E_87, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_168])).
% 2.54/1.64  tff(c_179, plain, (![E_87, A_89]: (~r2_hidden(E_87, A_89))), inference(splitLeft, [status(thm)], [c_174])).
% 2.54/1.64  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_156])).
% 2.54/1.64  tff(c_188, plain, (![F_91, D_92, C_93]: (F_91=D_92 | F_91=C_93 | ~r2_hidden(F_91, k2_tarski(C_93, D_92)))), inference(splitRight, [status(thm)], [c_174])).
% 2.54/1.64  tff(c_191, plain, (k1_mcart_1('#skF_7')='#skF_9' | k1_mcart_1('#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_156, c_188])).
% 2.54/1.64  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_120, c_191])).
% 2.54/1.64  tff(c_200, plain, (k2_mcart_1('#skF_7')='#skF_10'), inference(splitRight, [status(thm)], [c_48])).
% 2.54/1.64  tff(c_50, plain, (k1_mcart_1('#skF_7')!='#skF_8' | k2_mcart_1('#skF_7')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.64  tff(c_206, plain, (k1_mcart_1('#skF_7')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_50])).
% 2.54/1.64  tff(c_199, plain, (k1_mcart_1('#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_48])).
% 2.54/1.64  tff(c_218, plain, (![A_96, B_97, C_98]: (r2_hidden(k1_mcart_1(A_96), B_97) | ~r2_hidden(A_96, k2_zfmisc_1(B_97, C_98)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.54/1.64  tff(c_221, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_tarski('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_42, c_218])).
% 2.54/1.64  tff(c_242, plain, (![E_109, F_110, A_111, B_112]: (r2_hidden(k4_tarski(E_109, F_110), k2_zfmisc_1(A_111, B_112)) | ~r2_hidden(F_110, B_112) | ~r2_hidden(E_109, A_111))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.54/1.64  tff(c_246, plain, (![A_111, F_110, D_46, E_109, C_45]: (k2_mcart_1(k4_tarski(E_109, F_110))=D_46 | k2_mcart_1(k4_tarski(E_109, F_110))=C_45 | ~r2_hidden(F_110, k2_tarski(C_45, D_46)) | ~r2_hidden(E_109, A_111))), inference(resolution, [status(thm)], [c_242, c_34])).
% 2.54/1.64  tff(c_252, plain, (![A_111, F_110, D_46, E_109, C_45]: (F_110=D_46 | F_110=C_45 | ~r2_hidden(F_110, k2_tarski(C_45, D_46)) | ~r2_hidden(E_109, A_111))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_246])).
% 2.54/1.64  tff(c_257, plain, (![E_109, A_111]: (~r2_hidden(E_109, A_111))), inference(splitLeft, [status(thm)], [c_252])).
% 2.54/1.64  tff(c_231, plain, (![A_102, C_103, B_104]: (r2_hidden(k2_mcart_1(A_102), C_103) | ~r2_hidden(A_102, k2_zfmisc_1(B_104, C_103)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.54/1.64  tff(c_233, plain, (r2_hidden(k2_mcart_1('#skF_7'), k2_tarski('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_42, c_231])).
% 2.54/1.64  tff(c_235, plain, (r2_hidden('#skF_10', k2_tarski('#skF_10', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_233])).
% 2.54/1.64  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257, c_235])).
% 2.54/1.64  tff(c_281, plain, (![F_116, D_117, C_118]: (F_116=D_117 | F_116=C_118 | ~r2_hidden(F_116, k2_tarski(C_118, D_117)))), inference(splitRight, [status(thm)], [c_252])).
% 2.54/1.64  tff(c_287, plain, (k1_mcart_1('#skF_7')='#skF_9' | k1_mcart_1('#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_221, c_281])).
% 2.54/1.64  tff(c_293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_206, c_199, c_287])).
% 2.54/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.64  
% 2.54/1.64  Inference rules
% 2.54/1.64  ----------------------
% 2.54/1.64  #Ref     : 0
% 2.54/1.64  #Sup     : 45
% 2.54/1.64  #Fact    : 0
% 2.54/1.64  #Define  : 0
% 2.54/1.64  #Split   : 4
% 2.54/1.64  #Chain   : 0
% 2.54/1.64  #Close   : 0
% 2.54/1.64  
% 2.54/1.64  Ordering : KBO
% 2.54/1.64  
% 2.54/1.64  Simplification rules
% 2.54/1.64  ----------------------
% 2.54/1.64  #Subsume      : 15
% 2.54/1.64  #Demod        : 24
% 2.54/1.64  #Tautology    : 29
% 2.54/1.64  #SimpNegUnit  : 17
% 2.54/1.64  #BackRed      : 7
% 2.54/1.64  
% 2.54/1.64  #Partial instantiations: 0
% 2.54/1.64  #Strategies tried      : 1
% 2.54/1.64  
% 2.54/1.64  Timing (in seconds)
% 2.54/1.64  ----------------------
% 2.54/1.64  Preprocessing        : 0.52
% 2.54/1.64  Parsing              : 0.27
% 2.54/1.64  CNF conversion       : 0.04
% 2.54/1.64  Main loop            : 0.32
% 2.54/1.64  Inferencing          : 0.11
% 2.54/1.64  Reduction            : 0.10
% 2.54/1.64  Demodulation         : 0.07
% 2.54/1.64  BG Simplification    : 0.03
% 2.54/1.64  Subsumption          : 0.05
% 2.54/1.64  Abstraction          : 0.03
% 2.54/1.64  MUC search           : 0.00
% 2.54/1.64  Cooper               : 0.00
% 2.54/1.64  Total                : 0.90
% 2.54/1.64  Index Insertion      : 0.00
% 2.54/1.64  Index Deletion       : 0.00
% 2.54/1.64  Index Matching       : 0.00
% 2.54/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
