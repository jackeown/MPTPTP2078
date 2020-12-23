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
% DateTime   : Thu Dec  3 10:06:14 EST 2020

% Result     : Theorem 6.29s
% Output     : CNFRefutation 6.58s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 164 expanded)
%              Number of leaves         :   30 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  179 ( 370 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_80,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_76,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_44,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [B_30,A_29] :
      ( r1_ordinal1(B_30,A_29)
      | r1_ordinal1(A_29,B_30)
      | ~ v3_ordinal1(B_30)
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_870,plain,(
    ! [B_30] :
      ( ~ v3_ordinal1(B_30)
      | r1_ordinal1(B_30,B_30) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_28])).

tff(c_34,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ r1_ordinal1(A_32,B_33)
      | ~ v3_ordinal1(B_33)
      | ~ v3_ordinal1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_903,plain,(
    ! [A_198,B_199] :
      ( r1_tarski(A_198,B_199)
      | ~ r1_ordinal1(A_198,B_199)
      | ~ v3_ordinal1(B_199)
      | ~ v3_ordinal1(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_79,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_38,plain,(
    ! [A_35] :
      ( v3_ordinal1(k1_ordinal1(A_35))
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_80,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_241,plain,(
    ! [A_89,B_90] :
      ( r1_tarski(A_89,B_90)
      | ~ r1_ordinal1(A_89,B_90)
      | ~ v3_ordinal1(B_90)
      | ~ v3_ordinal1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    ! [A_34] : r2_hidden(A_34,k1_ordinal1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_197,plain,(
    ! [C_79,B_80,A_81] :
      ( r2_hidden(C_79,B_80)
      | ~ r2_hidden(C_79,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_212,plain,(
    ! [A_34,B_80] :
      ( r2_hidden(A_34,B_80)
      | ~ r1_tarski(k1_ordinal1(A_34),B_80) ) ),
    inference(resolution,[status(thm)],[c_36,c_197])).

tff(c_637,plain,(
    ! [A_149,B_150] :
      ( r2_hidden(A_149,B_150)
      | ~ r1_ordinal1(k1_ordinal1(A_149),B_150)
      | ~ v3_ordinal1(B_150)
      | ~ v3_ordinal1(k1_ordinal1(A_149)) ) ),
    inference(resolution,[status(thm)],[c_241,c_212])).

tff(c_668,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_637])).

tff(c_679,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_668])).

tff(c_680,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_679])).

tff(c_683,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_680])).

tff(c_687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_683])).

tff(c_688,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_688])).

tff(c_692,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_794,plain,(
    ! [C_175,B_176,A_177] :
      ( r2_hidden(C_175,B_176)
      | ~ r2_hidden(C_175,A_177)
      | ~ r1_tarski(A_177,B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_817,plain,(
    ! [B_180] :
      ( r2_hidden('#skF_2',B_180)
      | ~ r1_tarski('#skF_3',B_180) ) ),
    inference(resolution,[status(thm)],[c_692,c_794])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_823,plain,(
    ! [B_2,B_180] :
      ( r2_hidden('#skF_2',B_2)
      | ~ r1_tarski(B_180,B_2)
      | ~ r1_tarski('#skF_3',B_180) ) ),
    inference(resolution,[status(thm)],[c_817,c_2])).

tff(c_1032,plain,(
    ! [B_209,A_210] :
      ( r2_hidden('#skF_2',B_209)
      | ~ r1_tarski('#skF_3',A_210)
      | ~ r1_ordinal1(A_210,B_209)
      | ~ v3_ordinal1(B_209)
      | ~ v3_ordinal1(A_210) ) ),
    inference(resolution,[status(thm)],[c_903,c_823])).

tff(c_1035,plain,(
    ! [B_209,B_33] :
      ( r2_hidden('#skF_2',B_209)
      | ~ r1_ordinal1(B_33,B_209)
      | ~ v3_ordinal1(B_209)
      | ~ r1_ordinal1('#skF_3',B_33)
      | ~ v3_ordinal1(B_33)
      | ~ v3_ordinal1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_1032])).

tff(c_2542,plain,(
    ! [B_368,B_369] :
      ( r2_hidden('#skF_2',B_368)
      | ~ r1_ordinal1(B_369,B_368)
      | ~ v3_ordinal1(B_368)
      | ~ r1_ordinal1('#skF_3',B_369)
      | ~ v3_ordinal1(B_369) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1035])).

tff(c_2836,plain,(
    ! [A_391,B_392] :
      ( r2_hidden('#skF_2',A_391)
      | ~ r1_ordinal1('#skF_3',B_392)
      | r1_ordinal1(A_391,B_392)
      | ~ v3_ordinal1(B_392)
      | ~ v3_ordinal1(A_391) ) ),
    inference(resolution,[status(thm)],[c_28,c_2542])).

tff(c_2865,plain,(
    ! [A_391] :
      ( r2_hidden('#skF_2',A_391)
      | r1_ordinal1(A_391,'#skF_3')
      | ~ v3_ordinal1(A_391)
      | ~ v3_ordinal1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_870,c_2836])).

tff(c_2908,plain,(
    ! [A_393] :
      ( r2_hidden('#skF_2',A_393)
      | r1_ordinal1(A_393,'#skF_3')
      | ~ v3_ordinal1(A_393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2865])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_742,plain,(
    ! [A_158,B_159] :
      ( ~ r2_hidden('#skF_1'(A_158,B_159),B_159)
      | r1_tarski(A_158,B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_747,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_742])).

tff(c_10,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1080,plain,(
    ! [A_215,B_216,C_217] :
      ( r1_tarski(k2_tarski(A_215,B_216),C_217)
      | ~ r2_hidden(B_216,C_217)
      | ~ r2_hidden(A_215,C_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1113,plain,(
    ! [A_9,C_217] :
      ( r1_tarski(k1_tarski(A_9),C_217)
      | ~ r2_hidden(A_9,C_217)
      | ~ r2_hidden(A_9,C_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1080])).

tff(c_30,plain,(
    ! [A_31] : k2_xboole_0(A_31,k1_tarski(A_31)) = k1_ordinal1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1194,plain,(
    ! [A_229,C_230,B_231] :
      ( r1_tarski(k2_xboole_0(A_229,C_230),B_231)
      | ~ r1_tarski(C_230,B_231)
      | ~ r1_tarski(A_229,B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1320,plain,(
    ! [A_247,B_248] :
      ( r1_tarski(k1_ordinal1(A_247),B_248)
      | ~ r1_tarski(k1_tarski(A_247),B_248)
      | ~ r1_tarski(A_247,B_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1194])).

tff(c_1358,plain,(
    ! [A_252,C_253] :
      ( r1_tarski(k1_ordinal1(A_252),C_253)
      | ~ r1_tarski(A_252,C_253)
      | ~ r2_hidden(A_252,C_253) ) ),
    inference(resolution,[status(thm)],[c_1113,c_1320])).

tff(c_64,plain,(
    ! [B_42,A_43] :
      ( ~ r1_tarski(B_42,A_43)
      | ~ r2_hidden(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    ! [A_34] : ~ r1_tarski(k1_ordinal1(A_34),A_34) ),
    inference(resolution,[status(thm)],[c_36,c_64])).

tff(c_1381,plain,(
    ! [C_253] :
      ( ~ r1_tarski(C_253,C_253)
      | ~ r2_hidden(C_253,C_253) ) ),
    inference(resolution,[status(thm)],[c_1358,c_68])).

tff(c_1390,plain,(
    ! [C_253] : ~ r2_hidden(C_253,C_253) ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_1381])).

tff(c_2922,plain,
    ( r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2908,c_1390])).

tff(c_2939,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2922])).

tff(c_872,plain,(
    ! [B_193,A_194] :
      ( r1_ordinal1(B_193,A_194)
      | r1_ordinal1(A_194,B_193)
      | ~ v3_ordinal1(B_193)
      | ~ v3_ordinal1(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_691,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_878,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_872,c_691])).

tff(c_884,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_878])).

tff(c_886,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_884])).

tff(c_889,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_886])).

tff(c_893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_889])).

tff(c_895,plain,(
    v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_884])).

tff(c_32,plain,(
    ! [A_32,B_33] :
      ( r1_ordinal1(A_32,B_33)
      | ~ r1_tarski(A_32,B_33)
      | ~ v3_ordinal1(B_33)
      | ~ v3_ordinal1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5163,plain,(
    ! [A_484,C_485] :
      ( r1_ordinal1(k1_ordinal1(A_484),C_485)
      | ~ v3_ordinal1(C_485)
      | ~ v3_ordinal1(k1_ordinal1(A_484))
      | ~ r1_tarski(A_484,C_485)
      | ~ r2_hidden(A_484,C_485) ) ),
    inference(resolution,[status(thm)],[c_1358,c_32])).

tff(c_5211,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_5163,c_691])).

tff(c_5247,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_895,c_42,c_5211])).

tff(c_5250,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_5247])).

tff(c_5254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2939,c_5250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:27:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.29/2.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.58/2.31  
% 6.58/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.58/2.31  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 6.58/2.31  
% 6.58/2.31  %Foreground sorts:
% 6.58/2.31  
% 6.58/2.31  
% 6.58/2.31  %Background operators:
% 6.58/2.31  
% 6.58/2.31  
% 6.58/2.31  %Foreground operators:
% 6.58/2.31  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.58/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.58/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.58/2.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.58/2.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.58/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.58/2.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.58/2.31  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 6.58/2.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.58/2.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.58/2.31  tff('#skF_2', type, '#skF_2': $i).
% 6.58/2.31  tff('#skF_3', type, '#skF_3': $i).
% 6.58/2.31  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.58/2.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.58/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.58/2.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.58/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.58/2.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.58/2.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.58/2.31  
% 6.58/2.33  tff(f_95, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 6.58/2.33  tff(f_64, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 6.58/2.33  tff(f_74, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 6.58/2.33  tff(f_80, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 6.58/2.33  tff(f_76, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 6.58/2.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.58/2.33  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.58/2.33  tff(f_56, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.58/2.33  tff(f_66, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 6.58/2.33  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.58/2.33  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.58/2.33  tff(c_44, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.58/2.33  tff(c_42, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.58/2.33  tff(c_28, plain, (![B_30, A_29]: (r1_ordinal1(B_30, A_29) | r1_ordinal1(A_29, B_30) | ~v3_ordinal1(B_30) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.58/2.33  tff(c_870, plain, (![B_30]: (~v3_ordinal1(B_30) | r1_ordinal1(B_30, B_30))), inference(factorization, [status(thm), theory('equality')], [c_28])).
% 6.58/2.33  tff(c_34, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~r1_ordinal1(A_32, B_33) | ~v3_ordinal1(B_33) | ~v3_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.58/2.33  tff(c_903, plain, (![A_198, B_199]: (r1_tarski(A_198, B_199) | ~r1_ordinal1(A_198, B_199) | ~v3_ordinal1(B_199) | ~v3_ordinal1(A_198))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.58/2.33  tff(c_46, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.58/2.33  tff(c_79, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 6.58/2.33  tff(c_38, plain, (![A_35]: (v3_ordinal1(k1_ordinal1(A_35)) | ~v3_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.58/2.33  tff(c_52, plain, (r2_hidden('#skF_2', '#skF_3') | r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.58/2.33  tff(c_80, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 6.58/2.33  tff(c_241, plain, (![A_89, B_90]: (r1_tarski(A_89, B_90) | ~r1_ordinal1(A_89, B_90) | ~v3_ordinal1(B_90) | ~v3_ordinal1(A_89))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.58/2.33  tff(c_36, plain, (![A_34]: (r2_hidden(A_34, k1_ordinal1(A_34)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.58/2.33  tff(c_197, plain, (![C_79, B_80, A_81]: (r2_hidden(C_79, B_80) | ~r2_hidden(C_79, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.58/2.33  tff(c_212, plain, (![A_34, B_80]: (r2_hidden(A_34, B_80) | ~r1_tarski(k1_ordinal1(A_34), B_80))), inference(resolution, [status(thm)], [c_36, c_197])).
% 6.58/2.33  tff(c_637, plain, (![A_149, B_150]: (r2_hidden(A_149, B_150) | ~r1_ordinal1(k1_ordinal1(A_149), B_150) | ~v3_ordinal1(B_150) | ~v3_ordinal1(k1_ordinal1(A_149)))), inference(resolution, [status(thm)], [c_241, c_212])).
% 6.58/2.33  tff(c_668, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_80, c_637])).
% 6.58/2.33  tff(c_679, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_668])).
% 6.58/2.33  tff(c_680, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_79, c_679])).
% 6.58/2.33  tff(c_683, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_680])).
% 6.58/2.33  tff(c_687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_683])).
% 6.58/2.33  tff(c_688, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 6.58/2.33  tff(c_690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_688])).
% 6.58/2.33  tff(c_692, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 6.58/2.33  tff(c_794, plain, (![C_175, B_176, A_177]: (r2_hidden(C_175, B_176) | ~r2_hidden(C_175, A_177) | ~r1_tarski(A_177, B_176))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.58/2.33  tff(c_817, plain, (![B_180]: (r2_hidden('#skF_2', B_180) | ~r1_tarski('#skF_3', B_180))), inference(resolution, [status(thm)], [c_692, c_794])).
% 6.58/2.33  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.58/2.33  tff(c_823, plain, (![B_2, B_180]: (r2_hidden('#skF_2', B_2) | ~r1_tarski(B_180, B_2) | ~r1_tarski('#skF_3', B_180))), inference(resolution, [status(thm)], [c_817, c_2])).
% 6.58/2.33  tff(c_1032, plain, (![B_209, A_210]: (r2_hidden('#skF_2', B_209) | ~r1_tarski('#skF_3', A_210) | ~r1_ordinal1(A_210, B_209) | ~v3_ordinal1(B_209) | ~v3_ordinal1(A_210))), inference(resolution, [status(thm)], [c_903, c_823])).
% 6.58/2.33  tff(c_1035, plain, (![B_209, B_33]: (r2_hidden('#skF_2', B_209) | ~r1_ordinal1(B_33, B_209) | ~v3_ordinal1(B_209) | ~r1_ordinal1('#skF_3', B_33) | ~v3_ordinal1(B_33) | ~v3_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_1032])).
% 6.58/2.33  tff(c_2542, plain, (![B_368, B_369]: (r2_hidden('#skF_2', B_368) | ~r1_ordinal1(B_369, B_368) | ~v3_ordinal1(B_368) | ~r1_ordinal1('#skF_3', B_369) | ~v3_ordinal1(B_369))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1035])).
% 6.58/2.33  tff(c_2836, plain, (![A_391, B_392]: (r2_hidden('#skF_2', A_391) | ~r1_ordinal1('#skF_3', B_392) | r1_ordinal1(A_391, B_392) | ~v3_ordinal1(B_392) | ~v3_ordinal1(A_391))), inference(resolution, [status(thm)], [c_28, c_2542])).
% 6.58/2.33  tff(c_2865, plain, (![A_391]: (r2_hidden('#skF_2', A_391) | r1_ordinal1(A_391, '#skF_3') | ~v3_ordinal1(A_391) | ~v3_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_870, c_2836])).
% 6.58/2.33  tff(c_2908, plain, (![A_393]: (r2_hidden('#skF_2', A_393) | r1_ordinal1(A_393, '#skF_3') | ~v3_ordinal1(A_393))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2865])).
% 6.58/2.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.58/2.33  tff(c_742, plain, (![A_158, B_159]: (~r2_hidden('#skF_1'(A_158, B_159), B_159) | r1_tarski(A_158, B_159))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.58/2.33  tff(c_747, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_742])).
% 6.58/2.33  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.58/2.33  tff(c_1080, plain, (![A_215, B_216, C_217]: (r1_tarski(k2_tarski(A_215, B_216), C_217) | ~r2_hidden(B_216, C_217) | ~r2_hidden(A_215, C_217))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.58/2.33  tff(c_1113, plain, (![A_9, C_217]: (r1_tarski(k1_tarski(A_9), C_217) | ~r2_hidden(A_9, C_217) | ~r2_hidden(A_9, C_217))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1080])).
% 6.58/2.33  tff(c_30, plain, (![A_31]: (k2_xboole_0(A_31, k1_tarski(A_31))=k1_ordinal1(A_31))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.58/2.33  tff(c_1194, plain, (![A_229, C_230, B_231]: (r1_tarski(k2_xboole_0(A_229, C_230), B_231) | ~r1_tarski(C_230, B_231) | ~r1_tarski(A_229, B_231))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.58/2.33  tff(c_1320, plain, (![A_247, B_248]: (r1_tarski(k1_ordinal1(A_247), B_248) | ~r1_tarski(k1_tarski(A_247), B_248) | ~r1_tarski(A_247, B_248))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1194])).
% 6.58/2.33  tff(c_1358, plain, (![A_252, C_253]: (r1_tarski(k1_ordinal1(A_252), C_253) | ~r1_tarski(A_252, C_253) | ~r2_hidden(A_252, C_253))), inference(resolution, [status(thm)], [c_1113, c_1320])).
% 6.58/2.33  tff(c_64, plain, (![B_42, A_43]: (~r1_tarski(B_42, A_43) | ~r2_hidden(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.58/2.33  tff(c_68, plain, (![A_34]: (~r1_tarski(k1_ordinal1(A_34), A_34))), inference(resolution, [status(thm)], [c_36, c_64])).
% 6.58/2.33  tff(c_1381, plain, (![C_253]: (~r1_tarski(C_253, C_253) | ~r2_hidden(C_253, C_253))), inference(resolution, [status(thm)], [c_1358, c_68])).
% 6.58/2.33  tff(c_1390, plain, (![C_253]: (~r2_hidden(C_253, C_253))), inference(demodulation, [status(thm), theory('equality')], [c_747, c_1381])).
% 6.58/2.33  tff(c_2922, plain, (r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_2908, c_1390])).
% 6.58/2.33  tff(c_2939, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2922])).
% 6.58/2.33  tff(c_872, plain, (![B_193, A_194]: (r1_ordinal1(B_193, A_194) | r1_ordinal1(A_194, B_193) | ~v3_ordinal1(B_193) | ~v3_ordinal1(A_194))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.58/2.33  tff(c_691, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 6.58/2.33  tff(c_878, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_872, c_691])).
% 6.58/2.33  tff(c_884, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_878])).
% 6.58/2.33  tff(c_886, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_884])).
% 6.58/2.33  tff(c_889, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_886])).
% 6.58/2.33  tff(c_893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_889])).
% 6.58/2.33  tff(c_895, plain, (v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_884])).
% 6.58/2.33  tff(c_32, plain, (![A_32, B_33]: (r1_ordinal1(A_32, B_33) | ~r1_tarski(A_32, B_33) | ~v3_ordinal1(B_33) | ~v3_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.58/2.33  tff(c_5163, plain, (![A_484, C_485]: (r1_ordinal1(k1_ordinal1(A_484), C_485) | ~v3_ordinal1(C_485) | ~v3_ordinal1(k1_ordinal1(A_484)) | ~r1_tarski(A_484, C_485) | ~r2_hidden(A_484, C_485))), inference(resolution, [status(thm)], [c_1358, c_32])).
% 6.58/2.33  tff(c_5211, plain, (~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~r1_tarski('#skF_2', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_5163, c_691])).
% 6.58/2.33  tff(c_5247, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_692, c_895, c_42, c_5211])).
% 6.58/2.33  tff(c_5250, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_5247])).
% 6.58/2.33  tff(c_5254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2939, c_5250])).
% 6.58/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.58/2.33  
% 6.58/2.33  Inference rules
% 6.58/2.33  ----------------------
% 6.58/2.33  #Ref     : 0
% 6.58/2.33  #Sup     : 996
% 6.58/2.33  #Fact    : 6
% 6.58/2.33  #Define  : 0
% 6.58/2.33  #Split   : 14
% 6.58/2.33  #Chain   : 0
% 6.58/2.33  #Close   : 0
% 6.58/2.33  
% 6.58/2.33  Ordering : KBO
% 6.58/2.33  
% 6.58/2.33  Simplification rules
% 6.58/2.33  ----------------------
% 6.58/2.33  #Subsume      : 291
% 6.58/2.33  #Demod        : 539
% 6.58/2.33  #Tautology    : 105
% 6.58/2.33  #SimpNegUnit  : 4
% 6.58/2.33  #BackRed      : 0
% 6.58/2.33  
% 6.58/2.33  #Partial instantiations: 0
% 6.58/2.33  #Strategies tried      : 1
% 6.58/2.33  
% 6.58/2.33  Timing (in seconds)
% 6.58/2.33  ----------------------
% 6.58/2.33  Preprocessing        : 0.31
% 6.58/2.33  Parsing              : 0.16
% 6.58/2.33  CNF conversion       : 0.02
% 6.58/2.33  Main loop            : 1.24
% 6.58/2.33  Inferencing          : 0.43
% 6.58/2.33  Reduction            : 0.36
% 6.58/2.33  Demodulation         : 0.24
% 6.58/2.33  BG Simplification    : 0.04
% 6.58/2.33  Subsumption          : 0.32
% 6.58/2.33  Abstraction          : 0.05
% 6.58/2.33  MUC search           : 0.00
% 6.58/2.33  Cooper               : 0.00
% 6.58/2.33  Total                : 1.59
% 6.58/2.33  Index Insertion      : 0.00
% 6.58/2.33  Index Deletion       : 0.00
% 6.58/2.33  Index Matching       : 0.00
% 6.58/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
