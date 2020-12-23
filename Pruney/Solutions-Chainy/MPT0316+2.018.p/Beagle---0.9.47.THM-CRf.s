%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:59 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 166 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  107 ( 300 expanded)
%              Number of equality atoms :   27 ( 110 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [C_34,B_35] : r1_tarski(k1_tarski(C_34),k2_tarski(B_35,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    ! [A_3] : r1_tarski(k1_tarski(A_3),k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_72])).

tff(c_1048,plain,(
    ! [A_183,B_184] :
      ( r2_hidden(A_183,B_184)
      | ~ r1_tarski(k1_tarski(A_183),B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1059,plain,(
    ! [A_3] : r2_hidden(A_3,k1_tarski(A_3)) ),
    inference(resolution,[status(thm)],[c_75,c_1048])).

tff(c_84,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | ~ r1_tarski(k1_tarski(A_40),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_95,plain,(
    ! [A_3] : r2_hidden(A_3,k1_tarski(A_3)) ),
    inference(resolution,[status(thm)],[c_75,c_84])).

tff(c_52,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_83,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_160,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_205,plain,(
    ! [A_67,C_68,B_69,D_70] :
      ( r2_hidden(A_67,C_68)
      | ~ r2_hidden(k4_tarski(A_67,B_69),k2_zfmisc_1(C_68,D_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_209,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_160,c_205])).

tff(c_162,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(k1_tarski(A_57),k1_tarski(B_58)) = k1_tarski(A_57)
      | B_58 = A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44,plain,(
    ! [B_29,A_28] :
      ( ~ r2_hidden(B_29,A_28)
      | k4_xboole_0(A_28,k1_tarski(B_29)) != A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_188,plain,(
    ! [B_58,A_57] :
      ( ~ r2_hidden(B_58,k1_tarski(A_57))
      | B_58 = A_57 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_44])).

tff(c_212,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_209,c_188])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_212])).

tff(c_218,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_223,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_223])).

tff(c_225,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_502,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( r2_hidden(k4_tarski(A_110,B_111),k2_zfmisc_1(C_112,D_113))
      | ~ r2_hidden(B_111,D_113)
      | ~ r2_hidden(A_110,C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_217,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_54,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_437,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_54])).

tff(c_438,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_437])).

tff(c_505,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_502,c_438])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_225,c_505])).

tff(c_526,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_534,plain,(
    ! [A_114,B_115] :
      ( r2_hidden(A_114,B_115)
      | ~ r1_tarski(k1_tarski(A_114),B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_545,plain,(
    ! [A_3] : r2_hidden(A_3,k1_tarski(A_3)) ),
    inference(resolution,[status(thm)],[c_75,c_534])).

tff(c_525,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_531,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_525])).

tff(c_610,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_58])).

tff(c_611,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_610])).

tff(c_651,plain,(
    ! [B_137,D_138,A_139,C_140] :
      ( r2_hidden(B_137,D_138)
      | ~ r2_hidden(k4_tarski(A_139,B_137),k2_zfmisc_1(C_140,D_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_654,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_611,c_651])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_531,c_654])).

tff(c_660,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_698,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_56])).

tff(c_699,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_660,c_698])).

tff(c_22,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(C_13,D_14))
      | ~ r2_hidden(B_12,D_14)
      | ~ r2_hidden(A_11,C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_659,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_1033,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_659,c_54])).

tff(c_1034,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_660,c_1033])).

tff(c_1037,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_1034])).

tff(c_1041,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_699,c_1037])).

tff(c_1043,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_50,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1088,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_1043,c_50])).

tff(c_1641,plain,(
    ! [A_270,B_271,C_272,D_273] :
      ( r2_hidden(k4_tarski(A_270,B_271),k2_zfmisc_1(C_272,D_273))
      | ~ r2_hidden(B_271,D_273)
      | ~ r2_hidden(A_270,C_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1042,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_48,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))
    | ~ r2_hidden('#skF_6','#skF_8')
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1343,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_1043,c_1042,c_48])).

tff(c_1644,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1641,c_1343])).

tff(c_1663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_1088,c_1644])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:18:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.56  
% 3.26/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.57  %$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.26/1.57  
% 3.26/1.57  %Foreground sorts:
% 3.26/1.57  
% 3.26/1.57  
% 3.26/1.57  %Background operators:
% 3.26/1.57  
% 3.26/1.57  
% 3.26/1.57  %Foreground operators:
% 3.26/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.26/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.26/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.26/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.26/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.26/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.57  
% 3.26/1.58  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.26/1.58  tff(f_44, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.26/1.58  tff(f_75, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 3.26/1.58  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 3.26/1.58  tff(f_56, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 3.26/1.58  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.26/1.58  tff(f_84, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.26/1.58  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.58  tff(c_72, plain, (![C_34, B_35]: (r1_tarski(k1_tarski(C_34), k2_tarski(B_35, C_34)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.26/1.58  tff(c_75, plain, (![A_3]: (r1_tarski(k1_tarski(A_3), k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_72])).
% 3.26/1.58  tff(c_1048, plain, (![A_183, B_184]: (r2_hidden(A_183, B_184) | ~r1_tarski(k1_tarski(A_183), B_184))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.26/1.58  tff(c_1059, plain, (![A_3]: (r2_hidden(A_3, k1_tarski(A_3)))), inference(resolution, [status(thm)], [c_75, c_1048])).
% 3.26/1.58  tff(c_84, plain, (![A_40, B_41]: (r2_hidden(A_40, B_41) | ~r1_tarski(k1_tarski(A_40), B_41))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.26/1.58  tff(c_95, plain, (![A_3]: (r2_hidden(A_3, k1_tarski(A_3)))), inference(resolution, [status(thm)], [c_75, c_84])).
% 3.26/1.58  tff(c_52, plain, ('#skF_3'='#skF_1' | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.26/1.58  tff(c_83, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_52])).
% 3.26/1.58  tff(c_58, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.26/1.58  tff(c_160, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_58])).
% 3.26/1.58  tff(c_205, plain, (![A_67, C_68, B_69, D_70]: (r2_hidden(A_67, C_68) | ~r2_hidden(k4_tarski(A_67, B_69), k2_zfmisc_1(C_68, D_70)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.26/1.58  tff(c_209, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_160, c_205])).
% 3.26/1.58  tff(c_162, plain, (![A_57, B_58]: (k4_xboole_0(k1_tarski(A_57), k1_tarski(B_58))=k1_tarski(A_57) | B_58=A_57)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.58  tff(c_44, plain, (![B_29, A_28]: (~r2_hidden(B_29, A_28) | k4_xboole_0(A_28, k1_tarski(B_29))!=A_28)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.26/1.58  tff(c_188, plain, (![B_58, A_57]: (~r2_hidden(B_58, k1_tarski(A_57)) | B_58=A_57)), inference(superposition, [status(thm), theory('equality')], [c_162, c_44])).
% 3.26/1.58  tff(c_212, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_209, c_188])).
% 3.26/1.58  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_212])).
% 3.26/1.58  tff(c_218, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitRight, [status(thm)], [c_58])).
% 3.26/1.58  tff(c_56, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.26/1.58  tff(c_223, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.26/1.58  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_223])).
% 3.26/1.58  tff(c_225, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 3.26/1.58  tff(c_502, plain, (![A_110, B_111, C_112, D_113]: (r2_hidden(k4_tarski(A_110, B_111), k2_zfmisc_1(C_112, D_113)) | ~r2_hidden(B_111, D_113) | ~r2_hidden(A_110, C_112))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.26/1.58  tff(c_217, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_58])).
% 3.26/1.58  tff(c_54, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.26/1.58  tff(c_437, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_54])).
% 3.26/1.58  tff(c_438, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_218, c_437])).
% 3.26/1.58  tff(c_505, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_502, c_438])).
% 3.26/1.58  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_225, c_505])).
% 3.26/1.58  tff(c_526, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_52])).
% 3.26/1.58  tff(c_534, plain, (![A_114, B_115]: (r2_hidden(A_114, B_115) | ~r1_tarski(k1_tarski(A_114), B_115))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.26/1.58  tff(c_545, plain, (![A_3]: (r2_hidden(A_3, k1_tarski(A_3)))), inference(resolution, [status(thm)], [c_75, c_534])).
% 3.26/1.58  tff(c_525, plain, (~r2_hidden('#skF_6', '#skF_8') | '#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_52])).
% 3.26/1.58  tff(c_531, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_525])).
% 3.26/1.58  tff(c_610, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_58])).
% 3.26/1.58  tff(c_611, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_610])).
% 3.26/1.58  tff(c_651, plain, (![B_137, D_138, A_139, C_140]: (r2_hidden(B_137, D_138) | ~r2_hidden(k4_tarski(A_139, B_137), k2_zfmisc_1(C_140, D_138)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.26/1.58  tff(c_654, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_611, c_651])).
% 3.26/1.58  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_531, c_654])).
% 3.26/1.58  tff(c_660, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(splitRight, [status(thm)], [c_610])).
% 3.26/1.58  tff(c_698, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_56])).
% 3.26/1.58  tff(c_699, plain, (r2_hidden('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_660, c_698])).
% 3.26/1.58  tff(c_22, plain, (![A_11, B_12, C_13, D_14]: (r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(C_13, D_14)) | ~r2_hidden(B_12, D_14) | ~r2_hidden(A_11, C_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.26/1.58  tff(c_659, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_610])).
% 3.26/1.58  tff(c_1033, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_659, c_54])).
% 3.26/1.58  tff(c_1034, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_660, c_1033])).
% 3.26/1.58  tff(c_1037, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_1034])).
% 3.26/1.58  tff(c_1041, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_545, c_699, c_1037])).
% 3.26/1.58  tff(c_1043, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_525])).
% 3.26/1.58  tff(c_50, plain, (r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.26/1.58  tff(c_1088, plain, (r2_hidden('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_526, c_1043, c_50])).
% 3.26/1.58  tff(c_1641, plain, (![A_270, B_271, C_272, D_273]: (r2_hidden(k4_tarski(A_270, B_271), k2_zfmisc_1(C_272, D_273)) | ~r2_hidden(B_271, D_273) | ~r2_hidden(A_270, C_272))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.26/1.58  tff(c_1042, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_525])).
% 3.26/1.58  tff(c_48, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')) | ~r2_hidden('#skF_6', '#skF_8') | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.26/1.58  tff(c_1343, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_1043, c_1042, c_48])).
% 3.26/1.58  tff(c_1644, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_1641, c_1343])).
% 3.26/1.58  tff(c_1663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1059, c_1088, c_1644])).
% 3.26/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.58  
% 3.26/1.58  Inference rules
% 3.26/1.58  ----------------------
% 3.26/1.58  #Ref     : 0
% 3.26/1.58  #Sup     : 387
% 3.26/1.58  #Fact    : 0
% 3.26/1.58  #Define  : 0
% 3.26/1.58  #Split   : 5
% 3.26/1.58  #Chain   : 0
% 3.26/1.58  #Close   : 0
% 3.26/1.58  
% 3.26/1.58  Ordering : KBO
% 3.26/1.58  
% 3.26/1.58  Simplification rules
% 3.26/1.58  ----------------------
% 3.26/1.58  #Subsume      : 18
% 3.26/1.58  #Demod        : 173
% 3.26/1.58  #Tautology    : 205
% 3.26/1.58  #SimpNegUnit  : 6
% 3.26/1.58  #BackRed      : 3
% 3.26/1.58  
% 3.26/1.58  #Partial instantiations: 0
% 3.26/1.58  #Strategies tried      : 1
% 3.26/1.58  
% 3.26/1.58  Timing (in seconds)
% 3.26/1.58  ----------------------
% 3.26/1.58  Preprocessing        : 0.31
% 3.26/1.58  Parsing              : 0.16
% 3.26/1.58  CNF conversion       : 0.02
% 3.26/1.58  Main loop            : 0.46
% 3.26/1.58  Inferencing          : 0.18
% 3.26/1.58  Reduction            : 0.15
% 3.26/1.58  Demodulation         : 0.11
% 3.26/1.58  BG Simplification    : 0.03
% 3.26/1.58  Subsumption          : 0.07
% 3.26/1.58  Abstraction          : 0.02
% 3.26/1.58  MUC search           : 0.00
% 3.26/1.58  Cooper               : 0.00
% 3.26/1.58  Total                : 0.80
% 3.26/1.58  Index Insertion      : 0.00
% 3.26/1.58  Index Deletion       : 0.00
% 3.26/1.58  Index Matching       : 0.00
% 3.26/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
