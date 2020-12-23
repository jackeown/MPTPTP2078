%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:03 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   50 (  75 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 ( 128 expanded)
%              Number of equality atoms :   31 (  72 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(c_50,plain,
    ( k1_mcart_1('#skF_7') != '#skF_9'
    | k2_mcart_1('#skF_7') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_80,plain,(
    k2_mcart_1('#skF_7') != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,(
    r2_hidden('#skF_7',k2_zfmisc_1(k2_tarski('#skF_8','#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_103,plain,(
    ! [A_66,C_67,B_68] :
      ( k2_mcart_1(A_66) = C_67
      | ~ r2_hidden(A_66,k2_zfmisc_1(B_68,k1_tarski(C_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_106,plain,(
    k2_mcart_1('#skF_7') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_48,c_103])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_106])).

tff(c_112,plain,(
    k2_mcart_1('#skF_7') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( k1_mcart_1('#skF_7') != '#skF_8'
    | k2_mcart_1('#skF_7') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_118,plain,(
    k1_mcart_1('#skF_7') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_52])).

tff(c_111,plain,(
    k1_mcart_1('#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_148,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_hidden(k1_mcart_1(A_80),B_81)
      | ~ r2_hidden(A_80,k2_zfmisc_1(B_81,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_151,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_tarski('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_48,c_148])).

tff(c_46,plain,(
    ! [A_51,B_52] : k2_mcart_1(k4_tarski(A_51,B_52)) = B_52 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [E_39,F_40,A_7,B_8] :
      ( r2_hidden(k4_tarski(E_39,F_40),k2_zfmisc_1(A_7,B_8))
      | ~ r2_hidden(F_40,B_8)
      | ~ r2_hidden(E_39,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_192,plain,(
    ! [A_93,D_94,C_95,B_96] :
      ( k2_mcart_1(A_93) = D_94
      | k2_mcart_1(A_93) = C_95
      | ~ r2_hidden(A_93,k2_zfmisc_1(B_96,k2_tarski(C_95,D_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_196,plain,(
    ! [F_40,C_95,A_7,D_94,E_39] :
      ( k2_mcart_1(k4_tarski(E_39,F_40)) = D_94
      | k2_mcart_1(k4_tarski(E_39,F_40)) = C_95
      | ~ r2_hidden(F_40,k2_tarski(C_95,D_94))
      | ~ r2_hidden(E_39,A_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_192])).

tff(c_201,plain,(
    ! [F_40,C_95,A_7,D_94,E_39] :
      ( F_40 = D_94
      | F_40 = C_95
      | ~ r2_hidden(F_40,k2_tarski(C_95,D_94))
      | ~ r2_hidden(E_39,A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_196])).

tff(c_226,plain,(
    ! [E_39,A_7] : ~ r2_hidden(E_39,A_7) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_151])).

tff(c_236,plain,(
    ! [F_100,D_101,C_102] :
      ( F_100 = D_101
      | F_100 = C_102
      | ~ r2_hidden(F_100,k2_tarski(C_102,D_101)) ) ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_243,plain,
    ( k1_mcart_1('#skF_7') = '#skF_9'
    | k1_mcart_1('#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_151,c_236])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_111,c_243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.31  
% 2.38/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.32  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 2.38/1.32  
% 2.38/1.32  %Foreground sorts:
% 2.38/1.32  
% 2.38/1.32  
% 2.38/1.32  %Background operators:
% 2.38/1.32  
% 2.38/1.32  
% 2.38/1.32  %Foreground operators:
% 2.38/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.38/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.38/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.38/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.38/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.38/1.32  tff('#skF_10', type, '#skF_10': $i).
% 2.38/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.38/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.38/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.38/1.32  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.38/1.32  tff('#skF_9', type, '#skF_9': $i).
% 2.38/1.32  tff('#skF_8', type, '#skF_8': $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.32  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.38/1.32  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.38/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.38/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.32  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.38/1.32  
% 2.38/1.33  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 2.38/1.33  tff(f_55, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 2.38/1.33  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.38/1.33  tff(f_67, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.38/1.33  tff(f_43, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.38/1.33  tff(f_63, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 2.38/1.33  tff(c_50, plain, (k1_mcart_1('#skF_7')!='#skF_9' | k2_mcart_1('#skF_7')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.38/1.33  tff(c_80, plain, (k2_mcart_1('#skF_7')!='#skF_10'), inference(splitLeft, [status(thm)], [c_50])).
% 2.38/1.33  tff(c_48, plain, (r2_hidden('#skF_7', k2_zfmisc_1(k2_tarski('#skF_8', '#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.38/1.33  tff(c_103, plain, (![A_66, C_67, B_68]: (k2_mcart_1(A_66)=C_67 | ~r2_hidden(A_66, k2_zfmisc_1(B_68, k1_tarski(C_67))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.38/1.33  tff(c_106, plain, (k2_mcart_1('#skF_7')='#skF_10'), inference(resolution, [status(thm)], [c_48, c_103])).
% 2.38/1.33  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_106])).
% 2.38/1.33  tff(c_112, plain, (k2_mcart_1('#skF_7')='#skF_10'), inference(splitRight, [status(thm)], [c_50])).
% 2.38/1.33  tff(c_52, plain, (k1_mcart_1('#skF_7')!='#skF_8' | k2_mcart_1('#skF_7')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.38/1.33  tff(c_118, plain, (k1_mcart_1('#skF_7')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_52])).
% 2.38/1.33  tff(c_111, plain, (k1_mcart_1('#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_50])).
% 2.38/1.33  tff(c_148, plain, (![A_80, B_81, C_82]: (r2_hidden(k1_mcart_1(A_80), B_81) | ~r2_hidden(A_80, k2_zfmisc_1(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.33  tff(c_151, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_tarski('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_48, c_148])).
% 2.38/1.33  tff(c_46, plain, (![A_51, B_52]: (k2_mcart_1(k4_tarski(A_51, B_52))=B_52)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.38/1.33  tff(c_8, plain, (![E_39, F_40, A_7, B_8]: (r2_hidden(k4_tarski(E_39, F_40), k2_zfmisc_1(A_7, B_8)) | ~r2_hidden(F_40, B_8) | ~r2_hidden(E_39, A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.33  tff(c_192, plain, (![A_93, D_94, C_95, B_96]: (k2_mcart_1(A_93)=D_94 | k2_mcart_1(A_93)=C_95 | ~r2_hidden(A_93, k2_zfmisc_1(B_96, k2_tarski(C_95, D_94))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.38/1.33  tff(c_196, plain, (![F_40, C_95, A_7, D_94, E_39]: (k2_mcart_1(k4_tarski(E_39, F_40))=D_94 | k2_mcart_1(k4_tarski(E_39, F_40))=C_95 | ~r2_hidden(F_40, k2_tarski(C_95, D_94)) | ~r2_hidden(E_39, A_7))), inference(resolution, [status(thm)], [c_8, c_192])).
% 2.38/1.33  tff(c_201, plain, (![F_40, C_95, A_7, D_94, E_39]: (F_40=D_94 | F_40=C_95 | ~r2_hidden(F_40, k2_tarski(C_95, D_94)) | ~r2_hidden(E_39, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_196])).
% 2.38/1.33  tff(c_226, plain, (![E_39, A_7]: (~r2_hidden(E_39, A_7))), inference(splitLeft, [status(thm)], [c_201])).
% 2.38/1.33  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_151])).
% 2.38/1.33  tff(c_236, plain, (![F_100, D_101, C_102]: (F_100=D_101 | F_100=C_102 | ~r2_hidden(F_100, k2_tarski(C_102, D_101)))), inference(splitRight, [status(thm)], [c_201])).
% 2.38/1.33  tff(c_243, plain, (k1_mcart_1('#skF_7')='#skF_9' | k1_mcart_1('#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_151, c_236])).
% 2.38/1.33  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_111, c_243])).
% 2.38/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.33  
% 2.38/1.33  Inference rules
% 2.38/1.33  ----------------------
% 2.38/1.33  #Ref     : 0
% 2.38/1.33  #Sup     : 37
% 2.38/1.33  #Fact    : 0
% 2.38/1.33  #Define  : 0
% 2.38/1.33  #Split   : 3
% 2.38/1.33  #Chain   : 0
% 2.38/1.33  #Close   : 0
% 2.38/1.33  
% 2.38/1.33  Ordering : KBO
% 2.38/1.33  
% 2.38/1.33  Simplification rules
% 2.38/1.33  ----------------------
% 2.38/1.33  #Subsume      : 17
% 2.38/1.33  #Demod        : 10
% 2.38/1.33  #Tautology    : 20
% 2.38/1.33  #SimpNegUnit  : 15
% 2.38/1.33  #BackRed      : 6
% 2.38/1.33  
% 2.38/1.33  #Partial instantiations: 0
% 2.38/1.33  #Strategies tried      : 1
% 2.38/1.33  
% 2.38/1.33  Timing (in seconds)
% 2.38/1.33  ----------------------
% 2.38/1.33  Preprocessing        : 0.34
% 2.38/1.33  Parsing              : 0.18
% 2.38/1.33  CNF conversion       : 0.03
% 2.38/1.33  Main loop            : 0.18
% 2.38/1.33  Inferencing          : 0.06
% 2.38/1.33  Reduction            : 0.06
% 2.38/1.33  Demodulation         : 0.04
% 2.38/1.33  BG Simplification    : 0.02
% 2.38/1.33  Subsumption          : 0.03
% 2.38/1.33  Abstraction          : 0.02
% 2.38/1.33  MUC search           : 0.00
% 2.38/1.33  Cooper               : 0.00
% 2.38/1.33  Total                : 0.55
% 2.38/1.33  Index Insertion      : 0.00
% 2.38/1.33  Index Deletion       : 0.00
% 2.38/1.33  Index Matching       : 0.00
% 2.38/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
