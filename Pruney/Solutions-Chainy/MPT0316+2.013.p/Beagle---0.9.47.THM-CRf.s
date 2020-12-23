%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:59 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 154 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 278 expanded)
%              Number of equality atoms :   32 ( 108 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1199,plain,(
    ! [B_150,A_151] :
      ( r2_hidden(B_150,A_151)
      | k3_xboole_0(A_151,k1_tarski(B_150)) != k1_tarski(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1204,plain,(
    ! [B_150] : r2_hidden(B_150,k1_tarski(B_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1199])).

tff(c_64,plain,(
    ! [B_24,A_25] :
      ( r2_hidden(B_24,A_25)
      | k3_xboole_0(A_25,k1_tarski(B_24)) != k1_tarski(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [B_24] : r2_hidden(B_24,k1_tarski(B_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_26,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_101,plain,(
    ! [A_31,C_32,B_33,D_34] :
      ( r2_hidden(A_31,C_32)
      | ~ r2_hidden(k4_tarski(A_31,B_33),k2_zfmisc_1(C_32,D_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_105,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_71,c_101])).

tff(c_162,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(k1_tarski(A_42),B_43) = k1_tarski(A_42)
      | k4_xboole_0(k1_tarski(A_42),B_43) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden(A_7,B_8)
      | k4_xboole_0(k1_tarski(A_7),B_8) != k1_tarski(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_268,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden(A_48,B_49)
      | k4_xboole_0(k1_tarski(A_48),B_49) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_8])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( B_14 = A_13
      | k4_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_332,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r2_hidden(A_51,k1_tarski(B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_18])).

tff(c_335,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_105,c_332])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_335])).

tff(c_344,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_349,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_30])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,D_12))
      | ~ r2_hidden(B_10,D_12)
      | ~ r2_hidden(A_9,C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_343,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_28,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_665,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_28])).

tff(c_666,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_665])).

tff(c_669,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_666])).

tff(c_673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_349,c_669])).

tff(c_675,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_704,plain,(
    ! [B_92,A_93] :
      ( r2_hidden(B_92,A_93)
      | k3_xboole_0(A_93,k1_tarski(B_92)) != k1_tarski(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_709,plain,(
    ! [B_92] : r2_hidden(B_92,k1_tarski(B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_704])).

tff(c_674,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_680,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_674])).

tff(c_711,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_32])).

tff(c_712,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_711])).

tff(c_748,plain,(
    ! [B_103,D_104,A_105,C_106] :
      ( r2_hidden(B_103,D_104)
      | ~ r2_hidden(k4_tarski(A_105,B_103),k2_zfmisc_1(C_106,D_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_751,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_712,c_748])).

tff(c_755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_751])).

tff(c_757,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(splitRight,[status(thm)],[c_711])).

tff(c_791,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_30])).

tff(c_792,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_757,c_791])).

tff(c_756,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_711])).

tff(c_1133,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_756,c_28])).

tff(c_1134,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_757,c_1133])).

tff(c_1137,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_1134])).

tff(c_1141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_792,c_1137])).

tff(c_1143,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_674])).

tff(c_24,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1165,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_1143,c_24])).

tff(c_1469,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( r2_hidden(k4_tarski(A_178,B_179),k2_zfmisc_1(C_180,D_181))
      | ~ r2_hidden(B_179,D_181)
      | ~ r2_hidden(A_178,C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1142,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_674])).

tff(c_22,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1367,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_1143,c_1142,c_22])).

tff(c_1472,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1469,c_1367])).

tff(c_1482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1204,c_1165,c_1472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:29:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.45  
% 2.76/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.45  %$ r2_hidden > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.76/1.45  
% 2.76/1.45  %Foreground sorts:
% 2.76/1.45  
% 2.76/1.45  
% 2.76/1.45  %Background operators:
% 2.76/1.45  
% 2.76/1.45  
% 2.76/1.45  %Foreground operators:
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.76/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.76/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.76/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.45  tff('#skF_8', type, '#skF_8': $i).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.45  
% 2.76/1.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.76/1.46  tff(f_33, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.76/1.46  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.76/1.46  tff(f_44, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.76/1.46  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 2.76/1.46  tff(f_38, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.76/1.46  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.76/1.46  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.46  tff(c_1199, plain, (![B_150, A_151]: (r2_hidden(B_150, A_151) | k3_xboole_0(A_151, k1_tarski(B_150))!=k1_tarski(B_150))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.46  tff(c_1204, plain, (![B_150]: (r2_hidden(B_150, k1_tarski(B_150)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1199])).
% 2.76/1.46  tff(c_64, plain, (![B_24, A_25]: (r2_hidden(B_24, A_25) | k3_xboole_0(A_25, k1_tarski(B_24))!=k1_tarski(B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.46  tff(c_69, plain, (![B_24]: (r2_hidden(B_24, k1_tarski(B_24)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_64])).
% 2.76/1.46  tff(c_26, plain, ('#skF_3'='#skF_1' | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.76/1.46  tff(c_42, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_26])).
% 2.76/1.46  tff(c_32, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.76/1.46  tff(c_71, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.76/1.46  tff(c_101, plain, (![A_31, C_32, B_33, D_34]: (r2_hidden(A_31, C_32) | ~r2_hidden(k4_tarski(A_31, B_33), k2_zfmisc_1(C_32, D_34)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.46  tff(c_105, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_71, c_101])).
% 2.76/1.46  tff(c_162, plain, (![A_42, B_43]: (k4_xboole_0(k1_tarski(A_42), B_43)=k1_tarski(A_42) | k4_xboole_0(k1_tarski(A_42), B_43)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.76/1.46  tff(c_8, plain, (![A_7, B_8]: (~r2_hidden(A_7, B_8) | k4_xboole_0(k1_tarski(A_7), B_8)!=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.76/1.46  tff(c_268, plain, (![A_48, B_49]: (~r2_hidden(A_48, B_49) | k4_xboole_0(k1_tarski(A_48), B_49)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_162, c_8])).
% 2.76/1.46  tff(c_18, plain, (![B_14, A_13]: (B_14=A_13 | k4_xboole_0(k1_tarski(A_13), k1_tarski(B_14))!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.76/1.46  tff(c_332, plain, (![B_50, A_51]: (B_50=A_51 | ~r2_hidden(A_51, k1_tarski(B_50)))), inference(superposition, [status(thm), theory('equality')], [c_268, c_18])).
% 2.76/1.46  tff(c_335, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_105, c_332])).
% 2.76/1.46  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_335])).
% 2.76/1.46  tff(c_344, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitRight, [status(thm)], [c_32])).
% 2.76/1.46  tff(c_30, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.76/1.46  tff(c_349, plain, (r2_hidden('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_344, c_30])).
% 2.76/1.46  tff(c_12, plain, (![A_9, B_10, C_11, D_12]: (r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, D_12)) | ~r2_hidden(B_10, D_12) | ~r2_hidden(A_9, C_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.46  tff(c_343, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 2.76/1.46  tff(c_28, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.76/1.46  tff(c_665, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_28])).
% 2.76/1.46  tff(c_666, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_344, c_665])).
% 2.76/1.46  tff(c_669, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_666])).
% 2.76/1.46  tff(c_673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_349, c_669])).
% 2.76/1.46  tff(c_675, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_26])).
% 2.76/1.46  tff(c_704, plain, (![B_92, A_93]: (r2_hidden(B_92, A_93) | k3_xboole_0(A_93, k1_tarski(B_92))!=k1_tarski(B_92))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.46  tff(c_709, plain, (![B_92]: (r2_hidden(B_92, k1_tarski(B_92)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_704])).
% 2.76/1.46  tff(c_674, plain, (~r2_hidden('#skF_6', '#skF_8') | '#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 2.76/1.46  tff(c_680, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_674])).
% 2.76/1.46  tff(c_711, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_675, c_32])).
% 2.76/1.46  tff(c_712, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_711])).
% 2.76/1.46  tff(c_748, plain, (![B_103, D_104, A_105, C_106]: (r2_hidden(B_103, D_104) | ~r2_hidden(k4_tarski(A_105, B_103), k2_zfmisc_1(C_106, D_104)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.46  tff(c_751, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_712, c_748])).
% 2.76/1.46  tff(c_755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_680, c_751])).
% 2.76/1.46  tff(c_757, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(splitRight, [status(thm)], [c_711])).
% 2.76/1.46  tff(c_791, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_675, c_30])).
% 2.76/1.46  tff(c_792, plain, (r2_hidden('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_757, c_791])).
% 2.76/1.46  tff(c_756, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_711])).
% 2.76/1.46  tff(c_1133, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_675, c_756, c_28])).
% 2.76/1.46  tff(c_1134, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_757, c_1133])).
% 2.76/1.46  tff(c_1137, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_1134])).
% 2.76/1.46  tff(c_1141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_709, c_792, c_1137])).
% 2.76/1.46  tff(c_1143, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_674])).
% 2.76/1.46  tff(c_24, plain, (r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.76/1.46  tff(c_1165, plain, (r2_hidden('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_675, c_1143, c_24])).
% 2.76/1.46  tff(c_1469, plain, (![A_178, B_179, C_180, D_181]: (r2_hidden(k4_tarski(A_178, B_179), k2_zfmisc_1(C_180, D_181)) | ~r2_hidden(B_179, D_181) | ~r2_hidden(A_178, C_180))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.46  tff(c_1142, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_674])).
% 2.76/1.46  tff(c_22, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')) | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.76/1.46  tff(c_1367, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_675, c_1143, c_1142, c_22])).
% 2.76/1.46  tff(c_1472, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_1469, c_1367])).
% 2.76/1.46  tff(c_1482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1204, c_1165, c_1472])).
% 2.76/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.46  
% 2.76/1.46  Inference rules
% 2.76/1.46  ----------------------
% 2.76/1.46  #Ref     : 0
% 2.76/1.46  #Sup     : 336
% 2.76/1.46  #Fact    : 4
% 2.76/1.46  #Define  : 0
% 2.76/1.46  #Split   : 5
% 2.76/1.46  #Chain   : 0
% 2.76/1.46  #Close   : 0
% 2.76/1.46  
% 2.76/1.46  Ordering : KBO
% 2.76/1.46  
% 2.76/1.46  Simplification rules
% 2.76/1.46  ----------------------
% 2.76/1.46  #Subsume      : 50
% 2.76/1.46  #Demod        : 88
% 2.76/1.46  #Tautology    : 142
% 2.76/1.46  #SimpNegUnit  : 6
% 2.76/1.46  #BackRed      : 0
% 2.76/1.46  
% 2.76/1.46  #Partial instantiations: 0
% 2.76/1.46  #Strategies tried      : 1
% 2.76/1.46  
% 2.76/1.46  Timing (in seconds)
% 2.76/1.46  ----------------------
% 3.13/1.47  Preprocessing        : 0.29
% 3.13/1.47  Parsing              : 0.15
% 3.13/1.47  CNF conversion       : 0.02
% 3.13/1.47  Main loop            : 0.42
% 3.13/1.47  Inferencing          : 0.17
% 3.13/1.47  Reduction            : 0.12
% 3.13/1.47  Demodulation         : 0.08
% 3.13/1.47  BG Simplification    : 0.03
% 3.13/1.47  Subsumption          : 0.07
% 3.13/1.47  Abstraction          : 0.02
% 3.13/1.47  MUC search           : 0.00
% 3.13/1.47  Cooper               : 0.00
% 3.13/1.47  Total                : 0.74
% 3.13/1.47  Index Insertion      : 0.00
% 3.13/1.47  Index Deletion       : 0.00
% 3.13/1.47  Index Matching       : 0.00
% 3.13/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
