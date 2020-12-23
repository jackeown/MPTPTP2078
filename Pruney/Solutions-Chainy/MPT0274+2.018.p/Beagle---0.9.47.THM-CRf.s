%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:14 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 160 expanded)
%              Number of leaves         :   28 (  65 expanded)
%              Depth                    :    6
%              Number of atoms          :  100 ( 267 expanded)
%              Number of equality atoms :   30 (  82 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
      <=> ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_10,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_195,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_172,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_285,plain,(
    ! [A_77,C_78,B_79] :
      ( r1_xboole_0(k2_tarski(A_77,C_78),B_79)
      | r2_hidden(C_78,B_79)
      | r2_hidden(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_342,plain,(
    ! [A_97,C_98,B_99] :
      ( k4_xboole_0(k2_tarski(A_97,C_98),B_99) = k2_tarski(A_97,C_98)
      | r2_hidden(C_98,B_99)
      | r2_hidden(A_97,B_99) ) ),
    inference(resolution,[status(thm)],[c_285,c_4])).

tff(c_30,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_334,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_351,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_334])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_172,c_351])).

tff(c_375,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_377,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_376,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_36,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_396,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_36])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_54,C_55,B_56] :
      ( ~ r2_hidden(A_54,C_55)
      | ~ r1_xboole_0(k2_tarski(A_54,B_56),C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_313,plain,(
    ! [A_85,B_86,B_87] :
      ( ~ r2_hidden(A_85,B_86)
      | k4_xboole_0(k2_tarski(A_85,B_87),B_86) != k2_tarski(A_85,B_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_319,plain,(
    ! [B_8,B_86,A_7] :
      ( ~ r2_hidden(B_8,B_86)
      | k4_xboole_0(k2_tarski(A_7,B_8),B_86) != k2_tarski(B_8,A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_313])).

tff(c_400,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_4') != k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_319])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_377,c_400])).

tff(c_412,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_514,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_36])).

tff(c_183,plain,(
    ! [A_63,C_64,B_65] :
      ( ~ r2_hidden(A_63,C_64)
      | ~ r1_xboole_0(k2_tarski(B_65,A_63),C_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_104])).

tff(c_320,plain,(
    ! [A_88,B_89,B_90] :
      ( ~ r2_hidden(A_88,B_89)
      | k4_xboole_0(k2_tarski(B_90,A_88),B_89) != k2_tarski(B_90,A_88) ) ),
    inference(resolution,[status(thm)],[c_6,c_183])).

tff(c_323,plain,(
    ! [B_8,B_89,A_7] :
      ( ~ r2_hidden(B_8,B_89)
      | k4_xboole_0(k2_tarski(B_8,A_7),B_89) != k2_tarski(A_7,B_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_320])).

tff(c_524,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | k2_tarski('#skF_5','#skF_4') != k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_323])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_412,c_524])).

tff(c_545,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_547,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_545])).

tff(c_546,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_638,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_40])).

tff(c_673,plain,(
    ! [A_131,B_132,B_133] :
      ( ~ r2_hidden(A_131,B_132)
      | k4_xboole_0(k2_tarski(B_133,A_131),B_132) != k2_tarski(B_133,A_131) ) ),
    inference(resolution,[status(thm)],[c_6,c_183])).

tff(c_676,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_673])).

tff(c_686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_676])).

tff(c_687,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_770,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_40])).

tff(c_803,plain,(
    ! [A_148,B_149,B_150] :
      ( ~ r2_hidden(A_148,B_149)
      | k4_xboole_0(k2_tarski(A_148,B_150),B_149) != k2_tarski(A_148,B_150) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_806,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_803])).

tff(c_816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_806])).

tff(c_817,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_819,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_817])).

tff(c_818,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_944,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_38])).

tff(c_831,plain,(
    ! [A_153,C_154,B_155] :
      ( ~ r2_hidden(A_153,C_154)
      | ~ r1_xboole_0(k2_tarski(B_155,A_153),C_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_104])).

tff(c_969,plain,(
    ! [A_173,B_174,B_175] :
      ( ~ r2_hidden(A_173,B_174)
      | k4_xboole_0(k2_tarski(B_175,A_173),B_174) != k2_tarski(B_175,A_173) ) ),
    inference(resolution,[status(thm)],[c_6,c_831])).

tff(c_972,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_969])).

tff(c_982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_972])).

tff(c_983,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_817])).

tff(c_1110,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_38])).

tff(c_1124,plain,(
    ! [A_195,B_196,B_197] :
      ( ~ r2_hidden(A_195,B_196)
      | k4_xboole_0(k2_tarski(A_195,B_197),B_196) != k2_tarski(A_195,B_197) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_1127,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_1124])).

tff(c_1137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_1127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:04:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.41  
% 2.71/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.41  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.71/1.41  
% 2.71/1.41  %Foreground sorts:
% 2.71/1.41  
% 2.71/1.41  
% 2.71/1.41  %Background operators:
% 2.71/1.41  
% 2.71/1.41  
% 2.71/1.41  %Foreground operators:
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.71/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.71/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.71/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.71/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.71/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.71/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.71/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.41  
% 2.92/1.43  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.92/1.43  tff(f_73, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.92/1.43  tff(f_64, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.92/1.43  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.92/1.43  tff(f_54, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.92/1.43  tff(c_10, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.43  tff(c_34, plain, (~r2_hidden('#skF_1', '#skF_3') | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.92/1.43  tff(c_195, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.92/1.43  tff(c_32, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.92/1.43  tff(c_172, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.92/1.43  tff(c_285, plain, (![A_77, C_78, B_79]: (r1_xboole_0(k2_tarski(A_77, C_78), B_79) | r2_hidden(C_78, B_79) | r2_hidden(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.92/1.43  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.43  tff(c_342, plain, (![A_97, C_98, B_99]: (k4_xboole_0(k2_tarski(A_97, C_98), B_99)=k2_tarski(A_97, C_98) | r2_hidden(C_98, B_99) | r2_hidden(A_97, B_99))), inference(resolution, [status(thm)], [c_285, c_4])).
% 2.92/1.43  tff(c_30, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2') | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.92/1.43  tff(c_334, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 2.92/1.43  tff(c_351, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_342, c_334])).
% 2.92/1.43  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_172, c_351])).
% 2.92/1.43  tff(c_375, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 2.92/1.43  tff(c_377, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_375])).
% 2.92/1.43  tff(c_376, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k2_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 2.92/1.43  tff(c_36, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.92/1.43  tff(c_396, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_36])).
% 2.92/1.43  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k4_xboole_0(A_3, B_4)!=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.43  tff(c_104, plain, (![A_54, C_55, B_56]: (~r2_hidden(A_54, C_55) | ~r1_xboole_0(k2_tarski(A_54, B_56), C_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.92/1.43  tff(c_313, plain, (![A_85, B_86, B_87]: (~r2_hidden(A_85, B_86) | k4_xboole_0(k2_tarski(A_85, B_87), B_86)!=k2_tarski(A_85, B_87))), inference(resolution, [status(thm)], [c_6, c_104])).
% 2.92/1.43  tff(c_319, plain, (![B_8, B_86, A_7]: (~r2_hidden(B_8, B_86) | k4_xboole_0(k2_tarski(A_7, B_8), B_86)!=k2_tarski(B_8, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_313])).
% 2.92/1.43  tff(c_400, plain, (~r2_hidden('#skF_5', '#skF_6') | k2_tarski('#skF_5', '#skF_4')!=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_396, c_319])).
% 2.92/1.43  tff(c_411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_377, c_400])).
% 2.92/1.43  tff(c_412, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_375])).
% 2.92/1.43  tff(c_514, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_36])).
% 2.92/1.43  tff(c_183, plain, (![A_63, C_64, B_65]: (~r2_hidden(A_63, C_64) | ~r1_xboole_0(k2_tarski(B_65, A_63), C_64))), inference(superposition, [status(thm), theory('equality')], [c_10, c_104])).
% 2.92/1.43  tff(c_320, plain, (![A_88, B_89, B_90]: (~r2_hidden(A_88, B_89) | k4_xboole_0(k2_tarski(B_90, A_88), B_89)!=k2_tarski(B_90, A_88))), inference(resolution, [status(thm)], [c_6, c_183])).
% 2.92/1.43  tff(c_323, plain, (![B_8, B_89, A_7]: (~r2_hidden(B_8, B_89) | k4_xboole_0(k2_tarski(B_8, A_7), B_89)!=k2_tarski(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_320])).
% 2.92/1.43  tff(c_524, plain, (~r2_hidden('#skF_4', '#skF_6') | k2_tarski('#skF_5', '#skF_4')!=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_514, c_323])).
% 2.92/1.43  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_412, c_524])).
% 2.92/1.43  tff(c_545, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 2.92/1.43  tff(c_547, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_545])).
% 2.92/1.43  tff(c_546, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.92/1.43  tff(c_40, plain, (~r2_hidden('#skF_1', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.92/1.43  tff(c_638, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_546, c_40])).
% 2.92/1.43  tff(c_673, plain, (![A_131, B_132, B_133]: (~r2_hidden(A_131, B_132) | k4_xboole_0(k2_tarski(B_133, A_131), B_132)!=k2_tarski(B_133, A_131))), inference(resolution, [status(thm)], [c_6, c_183])).
% 2.92/1.43  tff(c_676, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_638, c_673])).
% 2.92/1.43  tff(c_686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_547, c_676])).
% 2.92/1.43  tff(c_687, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_545])).
% 2.92/1.43  tff(c_770, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_546, c_40])).
% 2.92/1.43  tff(c_803, plain, (![A_148, B_149, B_150]: (~r2_hidden(A_148, B_149) | k4_xboole_0(k2_tarski(A_148, B_150), B_149)!=k2_tarski(A_148, B_150))), inference(resolution, [status(thm)], [c_6, c_104])).
% 2.92/1.43  tff(c_806, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_770, c_803])).
% 2.92/1.43  tff(c_816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_687, c_806])).
% 2.92/1.43  tff(c_817, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 2.92/1.43  tff(c_819, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_817])).
% 2.92/1.43  tff(c_818, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.92/1.43  tff(c_38, plain, (~r2_hidden('#skF_2', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.92/1.43  tff(c_944, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_818, c_38])).
% 2.92/1.43  tff(c_831, plain, (![A_153, C_154, B_155]: (~r2_hidden(A_153, C_154) | ~r1_xboole_0(k2_tarski(B_155, A_153), C_154))), inference(superposition, [status(thm), theory('equality')], [c_10, c_104])).
% 2.92/1.43  tff(c_969, plain, (![A_173, B_174, B_175]: (~r2_hidden(A_173, B_174) | k4_xboole_0(k2_tarski(B_175, A_173), B_174)!=k2_tarski(B_175, A_173))), inference(resolution, [status(thm)], [c_6, c_831])).
% 2.92/1.43  tff(c_972, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_944, c_969])).
% 2.92/1.43  tff(c_982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_819, c_972])).
% 2.92/1.43  tff(c_983, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_817])).
% 2.92/1.43  tff(c_1110, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_818, c_38])).
% 2.92/1.43  tff(c_1124, plain, (![A_195, B_196, B_197]: (~r2_hidden(A_195, B_196) | k4_xboole_0(k2_tarski(A_195, B_197), B_196)!=k2_tarski(A_195, B_197))), inference(resolution, [status(thm)], [c_6, c_104])).
% 2.92/1.43  tff(c_1127, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1110, c_1124])).
% 2.92/1.43  tff(c_1137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_983, c_1127])).
% 2.92/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.43  
% 2.92/1.43  Inference rules
% 2.92/1.43  ----------------------
% 2.92/1.43  #Ref     : 0
% 2.92/1.43  #Sup     : 272
% 2.92/1.43  #Fact    : 0
% 2.92/1.43  #Define  : 0
% 2.92/1.43  #Split   : 8
% 2.92/1.43  #Chain   : 0
% 2.92/1.43  #Close   : 0
% 2.92/1.43  
% 2.92/1.43  Ordering : KBO
% 2.92/1.43  
% 2.92/1.43  Simplification rules
% 2.92/1.43  ----------------------
% 2.92/1.43  #Subsume      : 42
% 2.92/1.43  #Demod        : 61
% 2.92/1.43  #Tautology    : 142
% 2.92/1.43  #SimpNegUnit  : 5
% 2.92/1.43  #BackRed      : 0
% 2.92/1.43  
% 2.92/1.43  #Partial instantiations: 0
% 2.92/1.43  #Strategies tried      : 1
% 2.92/1.43  
% 2.92/1.43  Timing (in seconds)
% 2.92/1.43  ----------------------
% 2.92/1.43  Preprocessing        : 0.31
% 2.92/1.43  Parsing              : 0.16
% 2.92/1.43  CNF conversion       : 0.02
% 2.92/1.43  Main loop            : 0.36
% 2.92/1.43  Inferencing          : 0.14
% 2.92/1.43  Reduction            : 0.12
% 2.92/1.43  Demodulation         : 0.10
% 2.92/1.43  BG Simplification    : 0.02
% 2.92/1.43  Subsumption          : 0.05
% 2.92/1.43  Abstraction          : 0.02
% 2.92/1.43  MUC search           : 0.00
% 2.92/1.43  Cooper               : 0.00
% 2.92/1.43  Total                : 0.71
% 2.92/1.43  Index Insertion      : 0.00
% 2.92/1.43  Index Deletion       : 0.00
% 2.92/1.43  Index Matching       : 0.00
% 2.92/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
