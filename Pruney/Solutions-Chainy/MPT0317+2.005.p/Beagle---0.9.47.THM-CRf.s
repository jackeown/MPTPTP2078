%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:00 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 154 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :    6
%              Number of atoms          :  101 ( 271 expanded)
%              Number of equality atoms :   32 ( 113 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

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

tff(c_40,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_79,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_101,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_106,plain,(
    ! [A_42,C_43,B_44,D_45] :
      ( r2_hidden(A_42,C_43)
      | ~ r2_hidden(k4_tarski(A_42,B_44),k2_zfmisc_1(C_43,D_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_109,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_101,c_106])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_109])).

tff(c_115,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_120,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_120])).

tff(c_122,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_61,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,(
    ! [B_30,A_31] : r2_hidden(B_30,k2_tarski(A_31,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_83,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_80])).

tff(c_32,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( r2_hidden(k4_tarski(A_14,B_15),k2_zfmisc_1(C_16,D_17))
      | ~ r2_hidden(B_15,D_17)
      | ~ r2_hidden(A_14,C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_123,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_114,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_178,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_44])).

tff(c_179,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_178])).

tff(c_182,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_179])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_83,c_182])).

tff(c_188,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_187,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_189,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_198,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_213,plain,(
    ! [B_71,D_72,A_73,C_74] :
      ( r2_hidden(B_71,D_72)
      | ~ r2_hidden(k4_tarski(A_73,B_71),k2_zfmisc_1(C_74,D_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_217,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_198,c_213])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_225,plain,(
    ! [E_79,C_80,B_81,A_82] :
      ( E_79 = C_80
      | E_79 = B_81
      | E_79 = A_82
      | ~ r2_hidden(E_79,k1_enumset1(A_82,B_81,C_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_244,plain,(
    ! [E_83,B_84,A_85] :
      ( E_83 = B_84
      | E_83 = A_85
      | E_83 = A_85
      | ~ r2_hidden(E_83,k2_tarski(A_85,B_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_225])).

tff(c_260,plain,(
    ! [E_86,A_87] :
      ( E_86 = A_87
      | E_86 = A_87
      | E_86 = A_87
      | ~ r2_hidden(E_86,k1_tarski(A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_244])).

tff(c_263,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_217,c_260])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_189,c_189,c_263])).

tff(c_272,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_293,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_48])).

tff(c_6,plain,(
    ! [E_7,A_1,C_3] : r2_hidden(E_7,k1_enumset1(A_1,E_7,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_192,plain,(
    ! [A_63,B_64] : r2_hidden(A_63,k2_tarski(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_6])).

tff(c_195,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_192])).

tff(c_271,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_350,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1('#skF_9',k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_44])).

tff(c_351,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_350])).

tff(c_354,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_351])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_195,c_354])).

tff(c_360,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_42,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_375,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_360,c_42])).

tff(c_369,plain,(
    ! [B_114,A_115] : r2_hidden(B_114,k2_tarski(A_115,B_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_372,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_369])).

tff(c_436,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( r2_hidden(k4_tarski(A_139,B_140),k2_zfmisc_1(C_141,D_142))
      | ~ r2_hidden(B_140,D_142)
      | ~ r2_hidden(A_139,C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_359,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_38,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_429,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_360,c_359,c_38])).

tff(c_439,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_436,c_429])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_372,c_439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.40  
% 2.40/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.40  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 2.40/1.40  
% 2.40/1.40  %Foreground sorts:
% 2.40/1.40  
% 2.40/1.40  
% 2.40/1.40  %Background operators:
% 2.40/1.40  
% 2.40/1.40  
% 2.40/1.40  %Foreground operators:
% 2.40/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.40/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.40/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.40/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.40/1.40  tff('#skF_10', type, '#skF_10': $i).
% 2.40/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.40/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.40/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.40/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.40/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.40/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.40  tff('#skF_9', type, '#skF_9': $i).
% 2.40/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.40/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.40/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.40/1.40  
% 2.40/1.41  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.40/1.41  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.40/1.41  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.40/1.41  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.40/1.41  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.40/1.41  tff(c_40, plain, ('#skF_6'='#skF_4' | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.41  tff(c_79, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_40])).
% 2.40/1.41  tff(c_46, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.41  tff(c_101, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_46])).
% 2.40/1.41  tff(c_106, plain, (![A_42, C_43, B_44, D_45]: (r2_hidden(A_42, C_43) | ~r2_hidden(k4_tarski(A_42, B_44), k2_zfmisc_1(C_43, D_45)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.40/1.41  tff(c_109, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_101, c_106])).
% 2.40/1.41  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_109])).
% 2.40/1.41  tff(c_115, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_46])).
% 2.40/1.41  tff(c_48, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.41  tff(c_120, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_48])).
% 2.40/1.41  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_120])).
% 2.40/1.41  tff(c_122, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 2.40/1.41  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.40/1.41  tff(c_61, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.40/1.41  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.40/1.41  tff(c_80, plain, (![B_30, A_31]: (r2_hidden(B_30, k2_tarski(A_31, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_4])).
% 2.40/1.41  tff(c_83, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_80])).
% 2.40/1.41  tff(c_32, plain, (![A_14, B_15, C_16, D_17]: (r2_hidden(k4_tarski(A_14, B_15), k2_zfmisc_1(C_16, D_17)) | ~r2_hidden(B_15, D_17) | ~r2_hidden(A_14, C_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.40/1.41  tff(c_123, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_48])).
% 2.40/1.41  tff(c_114, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.40/1.41  tff(c_44, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.41  tff(c_178, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_44])).
% 2.40/1.41  tff(c_179, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_123, c_178])).
% 2.40/1.41  tff(c_182, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_179])).
% 2.40/1.41  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_83, c_182])).
% 2.40/1.41  tff(c_188, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_40])).
% 2.40/1.41  tff(c_187, plain, ('#skF_10'!='#skF_8' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 2.40/1.41  tff(c_189, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_187])).
% 2.40/1.41  tff(c_198, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_46])).
% 2.40/1.41  tff(c_213, plain, (![B_71, D_72, A_73, C_74]: (r2_hidden(B_71, D_72) | ~r2_hidden(k4_tarski(A_73, B_71), k2_zfmisc_1(C_74, D_72)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.40/1.41  tff(c_217, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_198, c_213])).
% 2.40/1.41  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.40/1.41  tff(c_225, plain, (![E_79, C_80, B_81, A_82]: (E_79=C_80 | E_79=B_81 | E_79=A_82 | ~r2_hidden(E_79, k1_enumset1(A_82, B_81, C_80)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.40/1.41  tff(c_244, plain, (![E_83, B_84, A_85]: (E_83=B_84 | E_83=A_85 | E_83=A_85 | ~r2_hidden(E_83, k2_tarski(A_85, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_225])).
% 2.40/1.41  tff(c_260, plain, (![E_86, A_87]: (E_86=A_87 | E_86=A_87 | E_86=A_87 | ~r2_hidden(E_86, k1_tarski(A_87)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_244])).
% 2.40/1.41  tff(c_263, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_217, c_260])).
% 2.40/1.41  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_189, c_189, c_263])).
% 2.40/1.41  tff(c_272, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_46])).
% 2.40/1.41  tff(c_293, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_272, c_48])).
% 2.40/1.41  tff(c_6, plain, (![E_7, A_1, C_3]: (r2_hidden(E_7, k1_enumset1(A_1, E_7, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.40/1.41  tff(c_192, plain, (![A_63, B_64]: (r2_hidden(A_63, k2_tarski(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_6])).
% 2.40/1.41  tff(c_195, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_192])).
% 2.40/1.41  tff(c_271, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.40/1.41  tff(c_350, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1('#skF_9', k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_44])).
% 2.40/1.41  tff(c_351, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_272, c_350])).
% 2.40/1.41  tff(c_354, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_351])).
% 2.40/1.41  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_293, c_195, c_354])).
% 2.40/1.41  tff(c_360, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_187])).
% 2.40/1.41  tff(c_42, plain, (r2_hidden('#skF_3', '#skF_5') | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.41  tff(c_375, plain, (r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_360, c_42])).
% 2.40/1.41  tff(c_369, plain, (![B_114, A_115]: (r2_hidden(B_114, k2_tarski(A_115, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_4])).
% 2.40/1.41  tff(c_372, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_369])).
% 2.40/1.41  tff(c_436, plain, (![A_139, B_140, C_141, D_142]: (r2_hidden(k4_tarski(A_139, B_140), k2_zfmisc_1(C_141, D_142)) | ~r2_hidden(B_140, D_142) | ~r2_hidden(A_139, C_141))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.40/1.41  tff(c_359, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_187])).
% 2.40/1.41  tff(c_38, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))) | '#skF_10'!='#skF_8' | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.41  tff(c_429, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_360, c_359, c_38])).
% 2.40/1.41  tff(c_439, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_436, c_429])).
% 2.40/1.41  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_375, c_372, c_439])).
% 2.40/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.41  
% 2.40/1.41  Inference rules
% 2.40/1.41  ----------------------
% 2.40/1.41  #Ref     : 0
% 2.40/1.41  #Sup     : 78
% 2.40/1.41  #Fact    : 0
% 2.40/1.41  #Define  : 0
% 2.40/1.41  #Split   : 5
% 2.40/1.41  #Chain   : 0
% 2.40/1.41  #Close   : 0
% 2.40/1.41  
% 2.40/1.41  Ordering : KBO
% 2.40/1.41  
% 2.40/1.41  Simplification rules
% 2.40/1.41  ----------------------
% 2.40/1.41  #Subsume      : 7
% 2.40/1.41  #Demod        : 32
% 2.40/1.41  #Tautology    : 58
% 2.40/1.41  #SimpNegUnit  : 6
% 2.40/1.41  #BackRed      : 0
% 2.40/1.41  
% 2.40/1.42  #Partial instantiations: 0
% 2.40/1.42  #Strategies tried      : 1
% 2.40/1.42  
% 2.40/1.42  Timing (in seconds)
% 2.40/1.42  ----------------------
% 2.40/1.42  Preprocessing        : 0.35
% 2.40/1.42  Parsing              : 0.18
% 2.40/1.42  CNF conversion       : 0.03
% 2.40/1.42  Main loop            : 0.29
% 2.40/1.42  Inferencing          : 0.11
% 2.40/1.42  Reduction            : 0.08
% 2.40/1.42  Demodulation         : 0.06
% 2.40/1.42  BG Simplification    : 0.02
% 2.40/1.42  Subsumption          : 0.05
% 2.40/1.42  Abstraction          : 0.01
% 2.40/1.42  MUC search           : 0.00
% 2.40/1.42  Cooper               : 0.00
% 2.40/1.42  Total                : 0.69
% 2.40/1.42  Index Insertion      : 0.00
% 2.40/1.42  Index Deletion       : 0.00
% 2.40/1.42  Index Matching       : 0.00
% 2.40/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
