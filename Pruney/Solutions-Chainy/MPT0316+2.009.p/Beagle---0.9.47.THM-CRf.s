%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:58 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 184 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 322 expanded)
%              Number of equality atoms :   31 ( 130 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_384,plain,(
    ! [A_144,B_145] : k1_enumset1(A_144,A_144,B_145) = k2_tarski(A_144,B_145) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [A_27] : k1_enumset1(A_27,A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_400,plain,(
    ! [B_146] : k2_tarski(B_146,B_146) = k1_tarski(B_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_30])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_406,plain,(
    ! [B_146] : r2_hidden(B_146,k1_tarski(B_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_4])).

tff(c_212,plain,(
    ! [A_85,B_86] : k1_enumset1(A_85,A_85,B_86) = k2_tarski(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_228,plain,(
    ! [B_87] : k2_tarski(B_87,B_87) = k1_tarski(B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_30])).

tff(c_234,plain,(
    ! [B_87] : r2_hidden(B_87,k1_tarski(B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_4])).

tff(c_61,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,(
    ! [B_39] : k2_tarski(B_39,B_39) = k1_tarski(B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_30])).

tff(c_83,plain,(
    ! [B_39] : r2_hidden(B_39,k1_tarski(B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_4])).

tff(c_42,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_36,plain,(
    ! [A_28,C_30,B_29,D_31] :
      ( r2_hidden(A_28,C_30)
      | ~ r2_hidden(k4_tarski(A_28,B_29),k2_zfmisc_1(C_30,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_129,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_125,c_36])).

tff(c_68,plain,(
    ! [B_38] : k2_tarski(B_38,B_38) = k1_tarski(B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_30])).

tff(c_104,plain,(
    ! [D_44,B_45,A_46] :
      ( D_44 = B_45
      | D_44 = A_46
      | ~ r2_hidden(D_44,k2_tarski(A_46,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_107,plain,(
    ! [D_44,B_38] :
      ( D_44 = B_38
      | D_44 = B_38
      | ~ r2_hidden(D_44,k1_tarski(B_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_104])).

tff(c_132,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_129,c_107])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_132])).

tff(c_138,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_143,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_143])).

tff(c_145,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_32,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( r2_hidden(k4_tarski(A_28,B_29),k2_zfmisc_1(C_30,D_31))
      | ~ r2_hidden(B_29,D_31)
      | ~ r2_hidden(A_28,C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_146,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_137,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_193,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_44])).

tff(c_194,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_193])).

tff(c_197,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_194])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_145,c_197])).

tff(c_202,plain,
    ( ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_208,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_203,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_266,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_48])).

tff(c_267,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_283,plain,(
    ! [B_101,D_102,A_103,C_104] :
      ( r2_hidden(B_101,D_102)
      | ~ r2_hidden(k4_tarski(A_103,B_101),k2_zfmisc_1(C_104,D_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_286,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_267,c_283])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_286])).

tff(c_292,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_308,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_46])).

tff(c_309,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_308])).

tff(c_291,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_357,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_291,c_44])).

tff(c_358,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_357])).

tff(c_361,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_358])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_309,c_361])).

tff(c_367,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_40,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_369,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_40])).

tff(c_370,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_370])).

tff(c_377,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_471,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( r2_hidden(k4_tarski(A_173,B_174),k2_zfmisc_1(C_175,D_176))
      | ~ r2_hidden(B_174,D_176)
      | ~ r2_hidden(A_173,C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_366,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_38,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_452,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_367,c_366,c_38])).

tff(c_474,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_471,c_452])).

tff(c_484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_377,c_474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:58:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.29  
% 2.33/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.30  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.33/1.30  
% 2.33/1.30  %Foreground sorts:
% 2.33/1.30  
% 2.33/1.30  
% 2.33/1.30  %Background operators:
% 2.33/1.30  
% 2.33/1.30  
% 2.33/1.30  %Foreground operators:
% 2.33/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.33/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.33/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.33/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.33/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.33/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.30  tff('#skF_10', type, '#skF_10': $i).
% 2.33/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.33/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.33/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.30  tff('#skF_9', type, '#skF_9': $i).
% 2.33/1.30  tff('#skF_8', type, '#skF_8': $i).
% 2.33/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.33/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.30  
% 2.33/1.31  tff(f_36, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.33/1.31  tff(f_46, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.33/1.31  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.33/1.31  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.33/1.31  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.33/1.31  tff(c_384, plain, (![A_144, B_145]: (k1_enumset1(A_144, A_144, B_145)=k2_tarski(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.33/1.31  tff(c_30, plain, (![A_27]: (k1_enumset1(A_27, A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.33/1.31  tff(c_400, plain, (![B_146]: (k2_tarski(B_146, B_146)=k1_tarski(B_146))), inference(superposition, [status(thm), theory('equality')], [c_384, c_30])).
% 2.33/1.31  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.33/1.31  tff(c_406, plain, (![B_146]: (r2_hidden(B_146, k1_tarski(B_146)))), inference(superposition, [status(thm), theory('equality')], [c_400, c_4])).
% 2.33/1.31  tff(c_212, plain, (![A_85, B_86]: (k1_enumset1(A_85, A_85, B_86)=k2_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.33/1.31  tff(c_228, plain, (![B_87]: (k2_tarski(B_87, B_87)=k1_tarski(B_87))), inference(superposition, [status(thm), theory('equality')], [c_212, c_30])).
% 2.33/1.31  tff(c_234, plain, (![B_87]: (r2_hidden(B_87, k1_tarski(B_87)))), inference(superposition, [status(thm), theory('equality')], [c_228, c_4])).
% 2.33/1.31  tff(c_61, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.33/1.31  tff(c_77, plain, (![B_39]: (k2_tarski(B_39, B_39)=k1_tarski(B_39))), inference(superposition, [status(thm), theory('equality')], [c_61, c_30])).
% 2.33/1.31  tff(c_83, plain, (![B_39]: (r2_hidden(B_39, k1_tarski(B_39)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_4])).
% 2.33/1.31  tff(c_42, plain, ('#skF_5'='#skF_3' | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.31  tff(c_60, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_42])).
% 2.33/1.31  tff(c_48, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.31  tff(c_125, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.33/1.31  tff(c_36, plain, (![A_28, C_30, B_29, D_31]: (r2_hidden(A_28, C_30) | ~r2_hidden(k4_tarski(A_28, B_29), k2_zfmisc_1(C_30, D_31)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.31  tff(c_129, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_125, c_36])).
% 2.33/1.31  tff(c_68, plain, (![B_38]: (k2_tarski(B_38, B_38)=k1_tarski(B_38))), inference(superposition, [status(thm), theory('equality')], [c_61, c_30])).
% 2.33/1.31  tff(c_104, plain, (![D_44, B_45, A_46]: (D_44=B_45 | D_44=A_46 | ~r2_hidden(D_44, k2_tarski(A_46, B_45)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.33/1.31  tff(c_107, plain, (![D_44, B_38]: (D_44=B_38 | D_44=B_38 | ~r2_hidden(D_44, k1_tarski(B_38)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_104])).
% 2.33/1.31  tff(c_132, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_129, c_107])).
% 2.33/1.31  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_132])).
% 2.33/1.31  tff(c_138, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_48])).
% 2.33/1.31  tff(c_46, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.31  tff(c_143, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_46])).
% 2.33/1.31  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_143])).
% 2.33/1.31  tff(c_145, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_46])).
% 2.33/1.31  tff(c_32, plain, (![A_28, B_29, C_30, D_31]: (r2_hidden(k4_tarski(A_28, B_29), k2_zfmisc_1(C_30, D_31)) | ~r2_hidden(B_29, D_31) | ~r2_hidden(A_28, C_30))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.31  tff(c_146, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_46])).
% 2.33/1.31  tff(c_137, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 2.33/1.31  tff(c_44, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.31  tff(c_193, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_44])).
% 2.33/1.31  tff(c_194, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_146, c_193])).
% 2.33/1.31  tff(c_197, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_194])).
% 2.33/1.31  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_145, c_197])).
% 2.33/1.31  tff(c_202, plain, (~r2_hidden('#skF_8', '#skF_10') | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 2.33/1.31  tff(c_208, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_202])).
% 2.33/1.31  tff(c_203, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_42])).
% 2.33/1.31  tff(c_266, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_48])).
% 2.33/1.31  tff(c_267, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_266])).
% 2.33/1.31  tff(c_283, plain, (![B_101, D_102, A_103, C_104]: (r2_hidden(B_101, D_102) | ~r2_hidden(k4_tarski(A_103, B_101), k2_zfmisc_1(C_104, D_102)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.31  tff(c_286, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_267, c_283])).
% 2.33/1.31  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_286])).
% 2.33/1.31  tff(c_292, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_266])).
% 2.33/1.31  tff(c_308, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_46])).
% 2.33/1.31  tff(c_309, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_292, c_308])).
% 2.33/1.31  tff(c_291, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_266])).
% 2.33/1.31  tff(c_357, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_291, c_44])).
% 2.33/1.31  tff(c_358, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_292, c_357])).
% 2.33/1.31  tff(c_361, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_358])).
% 2.33/1.31  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_234, c_309, c_361])).
% 2.33/1.31  tff(c_367, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_202])).
% 2.33/1.31  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.31  tff(c_369, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_40])).
% 2.33/1.31  tff(c_370, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_369])).
% 2.33/1.31  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_367, c_370])).
% 2.33/1.31  tff(c_377, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_369])).
% 2.33/1.31  tff(c_471, plain, (![A_173, B_174, C_175, D_176]: (r2_hidden(k4_tarski(A_173, B_174), k2_zfmisc_1(C_175, D_176)) | ~r2_hidden(B_174, D_176) | ~r2_hidden(A_173, C_175))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.31  tff(c_366, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_202])).
% 2.33/1.31  tff(c_38, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.31  tff(c_452, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_367, c_366, c_38])).
% 2.33/1.31  tff(c_474, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_471, c_452])).
% 2.33/1.31  tff(c_484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_406, c_377, c_474])).
% 2.33/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.31  
% 2.33/1.31  Inference rules
% 2.33/1.31  ----------------------
% 2.33/1.31  #Ref     : 0
% 2.33/1.31  #Sup     : 87
% 2.33/1.31  #Fact    : 0
% 2.33/1.31  #Define  : 0
% 2.33/1.31  #Split   : 8
% 2.33/1.31  #Chain   : 0
% 2.33/1.31  #Close   : 0
% 2.33/1.31  
% 2.33/1.31  Ordering : KBO
% 2.33/1.31  
% 2.33/1.31  Simplification rules
% 2.33/1.31  ----------------------
% 2.33/1.31  #Subsume      : 6
% 2.33/1.31  #Demod        : 33
% 2.33/1.31  #Tautology    : 71
% 2.33/1.31  #SimpNegUnit  : 6
% 2.33/1.31  #BackRed      : 0
% 2.33/1.31  
% 2.33/1.31  #Partial instantiations: 0
% 2.33/1.31  #Strategies tried      : 1
% 2.33/1.31  
% 2.33/1.31  Timing (in seconds)
% 2.33/1.31  ----------------------
% 2.33/1.32  Preprocessing        : 0.30
% 2.33/1.32  Parsing              : 0.15
% 2.33/1.32  CNF conversion       : 0.02
% 2.33/1.32  Main loop            : 0.25
% 2.33/1.32  Inferencing          : 0.10
% 2.33/1.32  Reduction            : 0.07
% 2.33/1.32  Demodulation         : 0.05
% 2.33/1.32  BG Simplification    : 0.02
% 2.33/1.32  Subsumption          : 0.04
% 2.33/1.32  Abstraction          : 0.01
% 2.33/1.32  MUC search           : 0.00
% 2.33/1.32  Cooper               : 0.00
% 2.33/1.32  Total                : 0.59
% 2.33/1.32  Index Insertion      : 0.00
% 2.33/1.32  Index Deletion       : 0.00
% 2.33/1.32  Index Matching       : 0.00
% 2.33/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
