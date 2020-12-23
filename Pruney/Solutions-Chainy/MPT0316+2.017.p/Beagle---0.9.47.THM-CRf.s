%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:59 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 173 expanded)
%              Number of leaves         :   27 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 308 expanded)
%              Number of equality atoms :   26 ( 113 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_516,plain,(
    ! [A_159,B_160] :
      ( k4_xboole_0(k1_tarski(A_159),B_160) = k1_tarski(A_159)
      | r2_hidden(A_159,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [B_36] : k4_xboole_0(k1_tarski(B_36),k1_tarski(B_36)) != k1_tarski(B_36) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_540,plain,(
    ! [A_159] : r2_hidden(A_159,k1_tarski(A_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_26])).

tff(c_382,plain,(
    ! [A_119,B_120] :
      ( k4_xboole_0(k1_tarski(A_119),B_120) = k1_tarski(A_119)
      | r2_hidden(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_402,plain,(
    ! [A_119] : r2_hidden(A_119,k1_tarski(A_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_26])).

tff(c_71,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(k1_tarski(A_46),B_47) = k1_tarski(A_46)
      | r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_87,plain,(
    ! [A_46] : r2_hidden(A_46,k1_tarski(A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_26])).

tff(c_34,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_89,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_126,plain,(
    ! [A_53,C_54,B_55,D_56] :
      ( r2_hidden(A_53,C_54)
      | ~ r2_hidden(k4_tarski(A_53,B_55),k2_zfmisc_1(C_54,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_130,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_89,c_126])).

tff(c_92,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(k1_tarski(A_49),k1_tarski(B_50)) = k1_tarski(A_49)
      | B_50 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_29,B_30] :
      ( ~ r2_hidden(A_29,B_30)
      | k4_xboole_0(k1_tarski(A_29),B_30) != k1_tarski(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_115,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden(A_49,k1_tarski(B_50))
      | B_50 = A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_16])).

tff(c_138,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_130,c_115])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_138])).

tff(c_144,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_149,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_149])).

tff(c_152,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_20,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( r2_hidden(k4_tarski(A_31,B_32),k2_zfmisc_1(C_33,D_34))
      | ~ r2_hidden(B_32,D_34)
      | ~ r2_hidden(A_31,C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_143,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_36,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_234,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_36])).

tff(c_235,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_234])).

tff(c_238,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_235])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_152,c_238])).

tff(c_244,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_352,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_38])).

tff(c_353,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_243,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_259,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_270,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_40])).

tff(c_271,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_342,plain,(
    ! [B_113,D_114,A_115,C_116] :
      ( r2_hidden(B_113,D_114)
      | ~ r2_hidden(k4_tarski(A_115,B_113),k2_zfmisc_1(C_116,D_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_345,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_271,c_342])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_345])).

tff(c_351,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_351])).

tff(c_360,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_361,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_350,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_467,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_350,c_36])).

tff(c_468,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_467])).

tff(c_471,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_468])).

tff(c_475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_360,c_471])).

tff(c_477,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_32,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_245,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_245])).

tff(c_252,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_483,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_252])).

tff(c_573,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( r2_hidden(k4_tarski(A_177,B_178),k2_zfmisc_1(C_179,D_180))
      | ~ r2_hidden(B_178,D_180)
      | ~ r2_hidden(A_177,C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_476,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_30,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_572,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_477,c_476,c_30])).

tff(c_576,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_573,c_572])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_483,c_576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:30:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.33  
% 2.44/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.33  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.44/1.33  
% 2.44/1.33  %Foreground sorts:
% 2.44/1.33  
% 2.44/1.33  
% 2.44/1.33  %Background operators:
% 2.44/1.33  
% 2.44/1.33  
% 2.44/1.33  %Foreground operators:
% 2.44/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.44/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.44/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.44/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.44/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.44/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.44/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.44/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.44/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.33  tff('#skF_8', type, '#skF_8': $i).
% 2.44/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.33  
% 2.44/1.34  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.44/1.34  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.44/1.34  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.44/1.34  tff(f_50, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.44/1.34  tff(c_516, plain, (![A_159, B_160]: (k4_xboole_0(k1_tarski(A_159), B_160)=k1_tarski(A_159) | r2_hidden(A_159, B_160))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.34  tff(c_26, plain, (![B_36]: (k4_xboole_0(k1_tarski(B_36), k1_tarski(B_36))!=k1_tarski(B_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.44/1.34  tff(c_540, plain, (![A_159]: (r2_hidden(A_159, k1_tarski(A_159)))), inference(superposition, [status(thm), theory('equality')], [c_516, c_26])).
% 2.44/1.34  tff(c_382, plain, (![A_119, B_120]: (k4_xboole_0(k1_tarski(A_119), B_120)=k1_tarski(A_119) | r2_hidden(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.34  tff(c_402, plain, (![A_119]: (r2_hidden(A_119, k1_tarski(A_119)))), inference(superposition, [status(thm), theory('equality')], [c_382, c_26])).
% 2.44/1.34  tff(c_71, plain, (![A_46, B_47]: (k4_xboole_0(k1_tarski(A_46), B_47)=k1_tarski(A_46) | r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.34  tff(c_87, plain, (![A_46]: (r2_hidden(A_46, k1_tarski(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_26])).
% 2.44/1.34  tff(c_34, plain, ('#skF_3'='#skF_1' | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.44/1.34  tff(c_50, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_34])).
% 2.44/1.34  tff(c_40, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.44/1.34  tff(c_89, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.44/1.34  tff(c_126, plain, (![A_53, C_54, B_55, D_56]: (r2_hidden(A_53, C_54) | ~r2_hidden(k4_tarski(A_53, B_55), k2_zfmisc_1(C_54, D_56)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.34  tff(c_130, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_89, c_126])).
% 2.44/1.34  tff(c_92, plain, (![A_49, B_50]: (k4_xboole_0(k1_tarski(A_49), k1_tarski(B_50))=k1_tarski(A_49) | B_50=A_49)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.44/1.34  tff(c_16, plain, (![A_29, B_30]: (~r2_hidden(A_29, B_30) | k4_xboole_0(k1_tarski(A_29), B_30)!=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.34  tff(c_115, plain, (![A_49, B_50]: (~r2_hidden(A_49, k1_tarski(B_50)) | B_50=A_49)), inference(superposition, [status(thm), theory('equality')], [c_92, c_16])).
% 2.44/1.34  tff(c_138, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_130, c_115])).
% 2.44/1.34  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_138])).
% 2.44/1.34  tff(c_144, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitRight, [status(thm)], [c_40])).
% 2.44/1.34  tff(c_38, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.44/1.34  tff(c_149, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.44/1.34  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_149])).
% 2.44/1.34  tff(c_152, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 2.44/1.34  tff(c_20, plain, (![A_31, B_32, C_33, D_34]: (r2_hidden(k4_tarski(A_31, B_32), k2_zfmisc_1(C_33, D_34)) | ~r2_hidden(B_32, D_34) | ~r2_hidden(A_31, C_33))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.34  tff(c_143, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_40])).
% 2.44/1.34  tff(c_36, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.44/1.34  tff(c_234, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_36])).
% 2.44/1.34  tff(c_235, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_144, c_234])).
% 2.44/1.34  tff(c_238, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_235])).
% 2.44/1.34  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_152, c_238])).
% 2.44/1.34  tff(c_244, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_34])).
% 2.44/1.34  tff(c_352, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_38])).
% 2.44/1.34  tff(c_353, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_352])).
% 2.44/1.34  tff(c_243, plain, (~r2_hidden('#skF_6', '#skF_8') | '#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_34])).
% 2.44/1.34  tff(c_259, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_243])).
% 2.44/1.34  tff(c_270, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_40])).
% 2.44/1.34  tff(c_271, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_270])).
% 2.44/1.34  tff(c_342, plain, (![B_113, D_114, A_115, C_116]: (r2_hidden(B_113, D_114) | ~r2_hidden(k4_tarski(A_115, B_113), k2_zfmisc_1(C_116, D_114)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.34  tff(c_345, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_271, c_342])).
% 2.44/1.34  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_345])).
% 2.44/1.34  tff(c_351, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(splitRight, [status(thm)], [c_270])).
% 2.44/1.34  tff(c_359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_353, c_351])).
% 2.44/1.34  tff(c_360, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_352])).
% 2.44/1.34  tff(c_361, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(splitRight, [status(thm)], [c_352])).
% 2.44/1.34  tff(c_350, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_270])).
% 2.44/1.34  tff(c_467, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_350, c_36])).
% 2.44/1.34  tff(c_468, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_361, c_467])).
% 2.44/1.34  tff(c_471, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_468])).
% 2.44/1.34  tff(c_475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_402, c_360, c_471])).
% 2.44/1.34  tff(c_477, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_243])).
% 2.44/1.34  tff(c_32, plain, (r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.44/1.35  tff(c_245, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_32])).
% 2.44/1.35  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_244, c_245])).
% 2.44/1.35  tff(c_252, plain, (~r2_hidden('#skF_6', '#skF_8') | r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 2.44/1.35  tff(c_483, plain, (r2_hidden('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_252])).
% 2.44/1.35  tff(c_573, plain, (![A_177, B_178, C_179, D_180]: (r2_hidden(k4_tarski(A_177, B_178), k2_zfmisc_1(C_179, D_180)) | ~r2_hidden(B_178, D_180) | ~r2_hidden(A_177, C_179))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.35  tff(c_476, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_243])).
% 2.44/1.35  tff(c_30, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')) | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.44/1.35  tff(c_572, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_477, c_476, c_30])).
% 2.44/1.35  tff(c_576, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_573, c_572])).
% 2.44/1.35  tff(c_586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_540, c_483, c_576])).
% 2.44/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.35  
% 2.44/1.35  Inference rules
% 2.44/1.35  ----------------------
% 2.44/1.35  #Ref     : 0
% 2.44/1.35  #Sup     : 107
% 2.44/1.35  #Fact    : 0
% 2.44/1.35  #Define  : 0
% 2.44/1.35  #Split   : 8
% 2.44/1.35  #Chain   : 0
% 2.44/1.35  #Close   : 0
% 2.44/1.35  
% 2.44/1.35  Ordering : KBO
% 2.44/1.35  
% 2.44/1.35  Simplification rules
% 2.44/1.35  ----------------------
% 2.44/1.35  #Subsume      : 7
% 2.44/1.35  #Demod        : 27
% 2.44/1.35  #Tautology    : 90
% 2.44/1.35  #SimpNegUnit  : 5
% 2.44/1.35  #BackRed      : 0
% 2.44/1.35  
% 2.44/1.35  #Partial instantiations: 0
% 2.44/1.35  #Strategies tried      : 1
% 2.44/1.35  
% 2.44/1.35  Timing (in seconds)
% 2.44/1.35  ----------------------
% 2.44/1.35  Preprocessing        : 0.31
% 2.44/1.35  Parsing              : 0.16
% 2.44/1.35  CNF conversion       : 0.02
% 2.44/1.35  Main loop            : 0.28
% 2.44/1.35  Inferencing          : 0.12
% 2.44/1.35  Reduction            : 0.08
% 2.44/1.35  Demodulation         : 0.05
% 2.44/1.35  BG Simplification    : 0.02
% 2.44/1.35  Subsumption          : 0.04
% 2.44/1.35  Abstraction          : 0.02
% 2.44/1.35  MUC search           : 0.00
% 2.44/1.35  Cooper               : 0.00
% 2.44/1.35  Total                : 0.63
% 2.44/1.35  Index Insertion      : 0.00
% 2.44/1.35  Index Deletion       : 0.00
% 2.44/1.35  Index Matching       : 0.00
% 2.44/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
