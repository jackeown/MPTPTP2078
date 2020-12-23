%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:15 EST 2020

% Result     : Theorem 12.18s
% Output     : CNFRefutation 12.39s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 410 expanded)
%              Number of leaves         :   29 ( 140 expanded)
%              Depth                    :   11
%              Number of atoms          :  205 ( 901 expanded)
%              Number of equality atoms :   90 ( 603 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_103,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_74,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_70,plain,
    ( '#skF_6' != '#skF_8'
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_81,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_76,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_371,plain,(
    ! [C_86,A_87,B_88] :
      ( r1_tarski(k2_zfmisc_1(C_86,A_87),k2_zfmisc_1(C_86,B_88))
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_382,plain,(
    ! [A_87] :
      ( r1_tarski(k2_zfmisc_1('#skF_7',A_87),k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r1_tarski(A_87,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_371])).

tff(c_1037,plain,(
    ! [B_119,A_120,C_121] :
      ( ~ r1_tarski(k2_zfmisc_1(B_119,A_120),k2_zfmisc_1(C_121,A_120))
      | r1_tarski(B_119,C_121)
      | k1_xboole_0 = A_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1041,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_382,c_1037])).

tff(c_1101,plain,
    ( r1_tarski('#skF_7','#skF_5')
    | ~ r1_tarski('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1041])).

tff(c_1127,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1101])).

tff(c_34,plain,(
    ! [A_16] : k3_xboole_0(A_16,A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_68,plain,(
    ! [A_37,C_39,B_38,D_40] : k3_xboole_0(k2_zfmisc_1(A_37,C_39),k2_zfmisc_1(B_38,D_40)) = k2_zfmisc_1(k3_xboole_0(A_37,B_38),k3_xboole_0(C_39,D_40)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_14737,plain,(
    ! [A_468,C_469,B_470,D_471] : k3_xboole_0(k2_zfmisc_1(A_468,C_469),k2_zfmisc_1(B_470,D_471)) = k2_zfmisc_1(k3_xboole_0(A_468,B_470),k3_xboole_0(C_469,D_471)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_14832,plain,(
    ! [A_468,C_469] : k3_xboole_0(k2_zfmisc_1(A_468,C_469),k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1(k3_xboole_0(A_468,'#skF_7'),k3_xboole_0(C_469,'#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_14737])).

tff(c_14856,plain,(
    ! [A_468,C_469] : k2_zfmisc_1(k3_xboole_0(A_468,'#skF_7'),k3_xboole_0(C_469,'#skF_8')) = k2_zfmisc_1(k3_xboole_0(A_468,'#skF_5'),k3_xboole_0(C_469,'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_14832])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_241,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_17729,plain,(
    ! [A_558,B_559,B_560] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_558,B_559),B_560),A_558)
      | r1_tarski(k3_xboole_0(A_558,B_559),B_560) ) ),
    inference(resolution,[status(thm)],[c_241,c_14])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_17776,plain,(
    ! [A_561,B_562] : r1_tarski(k3_xboole_0(A_561,B_562),A_561) ),
    inference(resolution,[status(thm)],[c_17729,c_6])).

tff(c_19437,plain,(
    ! [A_601,B_602,C_603,D_604] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_601,B_602),k3_xboole_0(C_603,D_604)),k2_zfmisc_1(A_601,C_603)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_17776])).

tff(c_22312,plain,(
    ! [A_679,B_680,A_681,B_682] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_679,B_680),k3_xboole_0(A_681,B_682)),k2_zfmisc_1(A_679,B_682)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_19437])).

tff(c_23829,plain,(
    ! [A_720,C_721] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_720,'#skF_5'),k3_xboole_0(C_721,'#skF_6')),k2_zfmisc_1(A_720,'#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14856,c_22312])).

tff(c_23920,plain,(
    ! [C_722] : r1_tarski(k2_zfmisc_1('#skF_5',k3_xboole_0(C_722,'#skF_6')),k2_zfmisc_1('#skF_5','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_23829])).

tff(c_56,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_tarski(k2_zfmisc_1(A_28,B_29),k2_zfmisc_1(A_28,C_30))
      | r1_tarski(B_29,C_30)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_23923,plain,(
    ! [C_722] :
      ( r1_tarski(k3_xboole_0(C_722,'#skF_6'),'#skF_8')
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_23920,c_56])).

tff(c_23950,plain,(
    ! [C_723] : r1_tarski(k3_xboole_0(C_723,'#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_23923])).

tff(c_23972,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_23950])).

tff(c_23978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1127,c_23972])).

tff(c_23979,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1101])).

tff(c_40,plain,(
    ! [B_22,A_21] :
      ( B_22 = A_21
      | ~ r1_tarski(B_22,A_21)
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_23982,plain,
    ( '#skF_7' = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_23979,c_40])).

tff(c_23988,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_23982])).

tff(c_44,plain,(
    ! [B_22] : r1_tarski(B_22,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_23980,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1101])).

tff(c_23995,plain,
    ( '#skF_6' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_23980,c_40])).

tff(c_24095,plain,(
    ~ r1_tarski('#skF_8','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_23995])).

tff(c_25222,plain,(
    ! [A_760,C_761,B_762,D_763] : k3_xboole_0(k2_zfmisc_1(A_760,C_761),k2_zfmisc_1(B_762,D_763)) = k2_zfmisc_1(k3_xboole_0(A_760,B_762),k3_xboole_0(C_761,D_763)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_25296,plain,(
    ! [B_762,D_763] : k3_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1(B_762,D_763)) = k2_zfmisc_1(k3_xboole_0('#skF_7',B_762),k3_xboole_0('#skF_8',D_763)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_25222])).

tff(c_35882,plain,(
    ! [B_1020,D_1021] : k2_zfmisc_1(k3_xboole_0('#skF_7',B_1020),k3_xboole_0('#skF_8',D_1021)) = k2_zfmisc_1(k3_xboole_0('#skF_5',B_1020),k3_xboole_0('#skF_6',D_1021)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_25296])).

tff(c_29844,plain,(
    ! [A_873,B_874,B_875] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_873,B_874),B_875),A_873)
      | r1_tarski(k3_xboole_0(A_873,B_874),B_875) ) ),
    inference(resolution,[status(thm)],[c_241,c_14])).

tff(c_29891,plain,(
    ! [A_876,B_877] : r1_tarski(k3_xboole_0(A_876,B_877),A_876) ),
    inference(resolution,[status(thm)],[c_29844,c_6])).

tff(c_32886,plain,(
    ! [A_930,B_931,C_932,D_933] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_930,B_931),k3_xboole_0(C_932,D_933)),k2_zfmisc_1(A_930,C_932)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_29891])).

tff(c_32969,plain,(
    ! [A_930,B_931,A_1,B_2] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_930,B_931),k3_xboole_0(A_1,B_2)),k2_zfmisc_1(A_930,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_32886])).

tff(c_36448,plain,(
    ! [B_1030,D_1031] : r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_5',B_1030),k3_xboole_0('#skF_6',D_1031)),k2_zfmisc_1('#skF_7',D_1031)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35882,c_32969])).

tff(c_36530,plain,(
    ! [D_1032] : r1_tarski(k2_zfmisc_1('#skF_5',k3_xboole_0('#skF_6',D_1032)),k2_zfmisc_1('#skF_7',D_1032)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_36448])).

tff(c_36576,plain,(
    r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_36530])).

tff(c_24005,plain,(
    ! [A_724,B_725,C_726] :
      ( ~ r1_tarski(k2_zfmisc_1(A_724,B_725),k2_zfmisc_1(A_724,C_726))
      | r1_tarski(B_725,C_726)
      | k1_xboole_0 = A_724 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24050,plain,(
    ! [B_725] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_7',B_725),k2_zfmisc_1('#skF_5','#skF_6'))
      | r1_tarski(B_725,'#skF_8')
      | k1_xboole_0 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_24005])).

tff(c_25049,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_24050])).

tff(c_54,plain,(
    ! [B_27] : k2_zfmisc_1(k1_xboole_0,B_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_301,plain,(
    ! [A_79,C_80,B_81] :
      ( r1_tarski(k2_zfmisc_1(A_79,C_80),k2_zfmisc_1(B_81,C_80))
      | ~ r1_tarski(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_331,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k2_zfmisc_1(A_82,B_83),k1_xboole_0)
      | ~ r1_tarski(A_82,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_301])).

tff(c_342,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k1_xboole_0)
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_331])).

tff(c_448,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_342])).

tff(c_25072,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25049,c_448])).

tff(c_25089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_25072])).

tff(c_25091,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_24050])).

tff(c_24047,plain,(
    ! [C_726] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',C_726))
      | r1_tarski('#skF_8',C_726)
      | k1_xboole_0 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_24005])).

tff(c_27107,plain,(
    ! [C_726] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',C_726))
      | r1_tarski('#skF_8',C_726) ) ),
    inference(negUnitSimplification,[status(thm)],[c_25091,c_24047])).

tff(c_36633,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_36576,c_27107])).

tff(c_36645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24095,c_36633])).

tff(c_36646,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_23995])).

tff(c_379,plain,(
    ! [B_88] :
      ( r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',B_88))
      | ~ r1_tarski('#skF_8',B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_371])).

tff(c_1051,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_6'
    | ~ r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_379,c_1037])).

tff(c_1106,plain,
    ( r1_tarski('#skF_5','#skF_7')
    | ~ r1_tarski('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1051])).

tff(c_36664,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36646,c_1106])).

tff(c_36665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23988,c_36664])).

tff(c_36667,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_342])).

tff(c_48,plain,(
    ! [A_25] : r1_tarski(k1_xboole_0,A_25) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_169,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_174,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_48,c_169])).

tff(c_36682,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_36667,c_174])).

tff(c_36697,plain,(
    ! [B_27] : k2_zfmisc_1('#skF_7',B_27) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36682,c_36682,c_54])).

tff(c_36770,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36697,c_76])).

tff(c_227,plain,(
    ! [B_63,A_64] :
      ( k1_xboole_0 = B_63
      | k1_xboole_0 = A_64
      | k2_zfmisc_1(A_64,B_63) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_230,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_227])).

tff(c_293,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_36693,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36682,c_293])).

tff(c_36843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36770,c_36693])).

tff(c_36844,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_36853,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_36844])).

tff(c_36861,plain,(
    '#skF_5' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36853,c_74])).

tff(c_36860,plain,(
    '#skF_6' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36853,c_72])).

tff(c_36845,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_36874,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36853,c_36845])).

tff(c_50,plain,(
    ! [B_27,A_26] :
      ( k1_xboole_0 = B_27
      | k1_xboole_0 = A_26
      | k2_zfmisc_1(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_37036,plain,(
    ! [B_1058,A_1059] :
      ( B_1058 = '#skF_8'
      | A_1059 = '#skF_8'
      | k2_zfmisc_1(A_1059,B_1058) != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36853,c_36853,c_36853,c_50])).

tff(c_37045,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_36874,c_37036])).

tff(c_37053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36861,c_36860,c_37045])).

tff(c_37054,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_36844])).

tff(c_37062,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37054,c_72])).

tff(c_37077,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37054,c_36845])).

tff(c_37239,plain,(
    ! [B_1073,A_1074] :
      ( B_1073 = '#skF_7'
      | A_1074 = '#skF_7'
      | k2_zfmisc_1(A_1074,B_1073) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37054,c_37054,c_37054,c_50])).

tff(c_37248,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_7' = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_37077,c_37239])).

tff(c_37256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_37062,c_37248])).

tff(c_37257,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_37258,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_37263,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37258,c_76])).

tff(c_37553,plain,(
    ! [A_1117,C_1118,B_1119] :
      ( r1_tarski(k2_zfmisc_1(A_1117,C_1118),k2_zfmisc_1(B_1119,C_1118))
      | ~ r1_tarski(A_1117,B_1119) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_37573,plain,(
    ! [B_1119] :
      ( r1_tarski(k2_zfmisc_1('#skF_5','#skF_8'),k2_zfmisc_1(B_1119,'#skF_6'))
      | ~ r1_tarski('#skF_5',B_1119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37263,c_37553])).

tff(c_38828,plain,(
    ! [A_1171,B_1172,C_1173] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1171,B_1172),k2_zfmisc_1(A_1171,C_1173))
      | r1_tarski(B_1172,C_1173)
      | k1_xboole_0 = A_1171 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_38847,plain,
    ( r1_tarski('#skF_8','#skF_6')
    | k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_37573,c_38828])).

tff(c_38917,plain,
    ( r1_tarski('#skF_8','#skF_6')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38847])).

tff(c_38918,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_38917])).

tff(c_37576,plain,(
    ! [A_1117] :
      ( r1_tarski(k2_zfmisc_1(A_1117,'#skF_6'),k2_zfmisc_1('#skF_5','#skF_8'))
      | ~ r1_tarski(A_1117,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37263,c_37553])).

tff(c_38854,plain,
    ( r1_tarski('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_37576,c_38828])).

tff(c_38924,plain,
    ( r1_tarski('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38854])).

tff(c_38925,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_38924])).

tff(c_38960,plain,
    ( '#skF_6' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_38925,c_40])).

tff(c_38966,plain,(
    '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38918,c_38960])).

tff(c_38968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37257,c_38966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.18/5.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.39/5.41  
% 12.39/5.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.39/5.41  %$ r2_xboole_0 > r2_hidden > r1_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_4
% 12.39/5.41  
% 12.39/5.41  %Foreground sorts:
% 12.39/5.41  
% 12.39/5.41  
% 12.39/5.41  %Background operators:
% 12.39/5.41  
% 12.39/5.41  
% 12.39/5.41  %Foreground operators:
% 12.39/5.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.39/5.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.39/5.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.39/5.41  tff('#skF_7', type, '#skF_7': $i).
% 12.39/5.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.39/5.41  tff('#skF_5', type, '#skF_5': $i).
% 12.39/5.41  tff('#skF_6', type, '#skF_6': $i).
% 12.39/5.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.39/5.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 12.39/5.41  tff('#skF_8', type, '#skF_8': $i).
% 12.39/5.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.39/5.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.39/5.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.39/5.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.39/5.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.39/5.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.39/5.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.39/5.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.39/5.41  
% 12.39/5.43  tff(f_114, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 12.39/5.43  tff(f_97, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 12.39/5.43  tff(f_91, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 12.39/5.43  tff(f_52, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 12.39/5.43  tff(f_103, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 12.39/5.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.39/5.43  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.39/5.43  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 12.39/5.43  tff(f_68, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.39/5.43  tff(f_80, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.39/5.43  tff(f_74, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.39/5.43  tff(c_70, plain, ('#skF_6'!='#skF_8' | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.39/5.43  tff(c_81, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_70])).
% 12.39/5.43  tff(c_72, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.39/5.43  tff(c_76, plain, (k2_zfmisc_1('#skF_7', '#skF_8')=k2_zfmisc_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.39/5.43  tff(c_371, plain, (![C_86, A_87, B_88]: (r1_tarski(k2_zfmisc_1(C_86, A_87), k2_zfmisc_1(C_86, B_88)) | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.39/5.43  tff(c_382, plain, (![A_87]: (r1_tarski(k2_zfmisc_1('#skF_7', A_87), k2_zfmisc_1('#skF_5', '#skF_6')) | ~r1_tarski(A_87, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_371])).
% 12.39/5.43  tff(c_1037, plain, (![B_119, A_120, C_121]: (~r1_tarski(k2_zfmisc_1(B_119, A_120), k2_zfmisc_1(C_121, A_120)) | r1_tarski(B_119, C_121) | k1_xboole_0=A_120)), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.39/5.43  tff(c_1041, plain, (r1_tarski('#skF_7', '#skF_5') | k1_xboole_0='#skF_6' | ~r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_382, c_1037])).
% 12.39/5.43  tff(c_1101, plain, (r1_tarski('#skF_7', '#skF_5') | ~r1_tarski('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_72, c_1041])).
% 12.39/5.43  tff(c_1127, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_1101])).
% 12.39/5.43  tff(c_34, plain, (![A_16]: (k3_xboole_0(A_16, A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.39/5.43  tff(c_74, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.39/5.43  tff(c_68, plain, (![A_37, C_39, B_38, D_40]: (k3_xboole_0(k2_zfmisc_1(A_37, C_39), k2_zfmisc_1(B_38, D_40))=k2_zfmisc_1(k3_xboole_0(A_37, B_38), k3_xboole_0(C_39, D_40)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.39/5.43  tff(c_14737, plain, (![A_468, C_469, B_470, D_471]: (k3_xboole_0(k2_zfmisc_1(A_468, C_469), k2_zfmisc_1(B_470, D_471))=k2_zfmisc_1(k3_xboole_0(A_468, B_470), k3_xboole_0(C_469, D_471)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.39/5.43  tff(c_14832, plain, (![A_468, C_469]: (k3_xboole_0(k2_zfmisc_1(A_468, C_469), k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1(k3_xboole_0(A_468, '#skF_7'), k3_xboole_0(C_469, '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_76, c_14737])).
% 12.39/5.43  tff(c_14856, plain, (![A_468, C_469]: (k2_zfmisc_1(k3_xboole_0(A_468, '#skF_7'), k3_xboole_0(C_469, '#skF_8'))=k2_zfmisc_1(k3_xboole_0(A_468, '#skF_5'), k3_xboole_0(C_469, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_14832])).
% 12.39/5.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.39/5.43  tff(c_241, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.39/5.43  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.39/5.43  tff(c_17729, plain, (![A_558, B_559, B_560]: (r2_hidden('#skF_1'(k3_xboole_0(A_558, B_559), B_560), A_558) | r1_tarski(k3_xboole_0(A_558, B_559), B_560))), inference(resolution, [status(thm)], [c_241, c_14])).
% 12.39/5.43  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.39/5.43  tff(c_17776, plain, (![A_561, B_562]: (r1_tarski(k3_xboole_0(A_561, B_562), A_561))), inference(resolution, [status(thm)], [c_17729, c_6])).
% 12.39/5.43  tff(c_19437, plain, (![A_601, B_602, C_603, D_604]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_601, B_602), k3_xboole_0(C_603, D_604)), k2_zfmisc_1(A_601, C_603)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_17776])).
% 12.39/5.43  tff(c_22312, plain, (![A_679, B_680, A_681, B_682]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_679, B_680), k3_xboole_0(A_681, B_682)), k2_zfmisc_1(A_679, B_682)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_19437])).
% 12.39/5.43  tff(c_23829, plain, (![A_720, C_721]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_720, '#skF_5'), k3_xboole_0(C_721, '#skF_6')), k2_zfmisc_1(A_720, '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_14856, c_22312])).
% 12.39/5.43  tff(c_23920, plain, (![C_722]: (r1_tarski(k2_zfmisc_1('#skF_5', k3_xboole_0(C_722, '#skF_6')), k2_zfmisc_1('#skF_5', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_23829])).
% 12.39/5.43  tff(c_56, plain, (![A_28, B_29, C_30]: (~r1_tarski(k2_zfmisc_1(A_28, B_29), k2_zfmisc_1(A_28, C_30)) | r1_tarski(B_29, C_30) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.39/5.43  tff(c_23923, plain, (![C_722]: (r1_tarski(k3_xboole_0(C_722, '#skF_6'), '#skF_8') | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_23920, c_56])).
% 12.39/5.43  tff(c_23950, plain, (![C_723]: (r1_tarski(k3_xboole_0(C_723, '#skF_6'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_74, c_23923])).
% 12.39/5.43  tff(c_23972, plain, (r1_tarski('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_34, c_23950])).
% 12.39/5.43  tff(c_23978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1127, c_23972])).
% 12.39/5.43  tff(c_23979, plain, (r1_tarski('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_1101])).
% 12.39/5.43  tff(c_40, plain, (![B_22, A_21]: (B_22=A_21 | ~r1_tarski(B_22, A_21) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.39/5.43  tff(c_23982, plain, ('#skF_7'='#skF_5' | ~r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_23979, c_40])).
% 12.39/5.43  tff(c_23988, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_81, c_23982])).
% 12.39/5.43  tff(c_44, plain, (![B_22]: (r1_tarski(B_22, B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.39/5.43  tff(c_23980, plain, (r1_tarski('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_1101])).
% 12.39/5.43  tff(c_23995, plain, ('#skF_6'='#skF_8' | ~r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_23980, c_40])).
% 12.39/5.43  tff(c_24095, plain, (~r1_tarski('#skF_8', '#skF_6')), inference(splitLeft, [status(thm)], [c_23995])).
% 12.39/5.43  tff(c_25222, plain, (![A_760, C_761, B_762, D_763]: (k3_xboole_0(k2_zfmisc_1(A_760, C_761), k2_zfmisc_1(B_762, D_763))=k2_zfmisc_1(k3_xboole_0(A_760, B_762), k3_xboole_0(C_761, D_763)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.39/5.43  tff(c_25296, plain, (![B_762, D_763]: (k3_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1(B_762, D_763))=k2_zfmisc_1(k3_xboole_0('#skF_7', B_762), k3_xboole_0('#skF_8', D_763)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_25222])).
% 12.39/5.43  tff(c_35882, plain, (![B_1020, D_1021]: (k2_zfmisc_1(k3_xboole_0('#skF_7', B_1020), k3_xboole_0('#skF_8', D_1021))=k2_zfmisc_1(k3_xboole_0('#skF_5', B_1020), k3_xboole_0('#skF_6', D_1021)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_25296])).
% 12.39/5.43  tff(c_29844, plain, (![A_873, B_874, B_875]: (r2_hidden('#skF_1'(k3_xboole_0(A_873, B_874), B_875), A_873) | r1_tarski(k3_xboole_0(A_873, B_874), B_875))), inference(resolution, [status(thm)], [c_241, c_14])).
% 12.39/5.43  tff(c_29891, plain, (![A_876, B_877]: (r1_tarski(k3_xboole_0(A_876, B_877), A_876))), inference(resolution, [status(thm)], [c_29844, c_6])).
% 12.39/5.43  tff(c_32886, plain, (![A_930, B_931, C_932, D_933]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_930, B_931), k3_xboole_0(C_932, D_933)), k2_zfmisc_1(A_930, C_932)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_29891])).
% 12.39/5.43  tff(c_32969, plain, (![A_930, B_931, A_1, B_2]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_930, B_931), k3_xboole_0(A_1, B_2)), k2_zfmisc_1(A_930, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_32886])).
% 12.39/5.43  tff(c_36448, plain, (![B_1030, D_1031]: (r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_5', B_1030), k3_xboole_0('#skF_6', D_1031)), k2_zfmisc_1('#skF_7', D_1031)))), inference(superposition, [status(thm), theory('equality')], [c_35882, c_32969])).
% 12.39/5.43  tff(c_36530, plain, (![D_1032]: (r1_tarski(k2_zfmisc_1('#skF_5', k3_xboole_0('#skF_6', D_1032)), k2_zfmisc_1('#skF_7', D_1032)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_36448])).
% 12.39/5.43  tff(c_36576, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_36530])).
% 12.39/5.43  tff(c_24005, plain, (![A_724, B_725, C_726]: (~r1_tarski(k2_zfmisc_1(A_724, B_725), k2_zfmisc_1(A_724, C_726)) | r1_tarski(B_725, C_726) | k1_xboole_0=A_724)), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.39/5.43  tff(c_24050, plain, (![B_725]: (~r1_tarski(k2_zfmisc_1('#skF_7', B_725), k2_zfmisc_1('#skF_5', '#skF_6')) | r1_tarski(B_725, '#skF_8') | k1_xboole_0='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_76, c_24005])).
% 12.39/5.43  tff(c_25049, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_24050])).
% 12.39/5.43  tff(c_54, plain, (![B_27]: (k2_zfmisc_1(k1_xboole_0, B_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.39/5.43  tff(c_301, plain, (![A_79, C_80, B_81]: (r1_tarski(k2_zfmisc_1(A_79, C_80), k2_zfmisc_1(B_81, C_80)) | ~r1_tarski(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.39/5.43  tff(c_331, plain, (![A_82, B_83]: (r1_tarski(k2_zfmisc_1(A_82, B_83), k1_xboole_0) | ~r1_tarski(A_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_301])).
% 12.39/5.43  tff(c_342, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k1_xboole_0) | ~r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_76, c_331])).
% 12.39/5.43  tff(c_448, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_342])).
% 12.39/5.43  tff(c_25072, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_25049, c_448])).
% 12.39/5.43  tff(c_25089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_25072])).
% 12.39/5.43  tff(c_25091, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_24050])).
% 12.39/5.43  tff(c_24047, plain, (![C_726]: (~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', C_726)) | r1_tarski('#skF_8', C_726) | k1_xboole_0='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_76, c_24005])).
% 12.39/5.43  tff(c_27107, plain, (![C_726]: (~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', C_726)) | r1_tarski('#skF_8', C_726))), inference(negUnitSimplification, [status(thm)], [c_25091, c_24047])).
% 12.39/5.43  tff(c_36633, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_36576, c_27107])).
% 12.39/5.43  tff(c_36645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24095, c_36633])).
% 12.39/5.43  tff(c_36646, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_23995])).
% 12.39/5.43  tff(c_379, plain, (![B_88]: (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', B_88)) | ~r1_tarski('#skF_8', B_88))), inference(superposition, [status(thm), theory('equality')], [c_76, c_371])).
% 12.39/5.43  tff(c_1051, plain, (r1_tarski('#skF_5', '#skF_7') | k1_xboole_0='#skF_6' | ~r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_379, c_1037])).
% 12.39/5.43  tff(c_1106, plain, (r1_tarski('#skF_5', '#skF_7') | ~r1_tarski('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_72, c_1051])).
% 12.39/5.43  tff(c_36664, plain, (r1_tarski('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36646, c_1106])).
% 12.39/5.43  tff(c_36665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23988, c_36664])).
% 12.39/5.43  tff(c_36667, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_342])).
% 12.39/5.43  tff(c_48, plain, (![A_25]: (r1_tarski(k1_xboole_0, A_25))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.39/5.43  tff(c_169, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.39/5.43  tff(c_174, plain, (![A_25]: (k1_xboole_0=A_25 | ~r1_tarski(A_25, k1_xboole_0))), inference(resolution, [status(thm)], [c_48, c_169])).
% 12.39/5.43  tff(c_36682, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_36667, c_174])).
% 12.39/5.43  tff(c_36697, plain, (![B_27]: (k2_zfmisc_1('#skF_7', B_27)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36682, c_36682, c_54])).
% 12.39/5.43  tff(c_36770, plain, (k2_zfmisc_1('#skF_5', '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_36697, c_76])).
% 12.39/5.43  tff(c_227, plain, (![B_63, A_64]: (k1_xboole_0=B_63 | k1_xboole_0=A_64 | k2_zfmisc_1(A_64, B_63)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.39/5.43  tff(c_230, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_76, c_227])).
% 12.39/5.43  tff(c_293, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_230])).
% 12.39/5.43  tff(c_36693, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_36682, c_293])).
% 12.39/5.43  tff(c_36843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36770, c_36693])).
% 12.39/5.43  tff(c_36844, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_230])).
% 12.39/5.43  tff(c_36853, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_36844])).
% 12.39/5.43  tff(c_36861, plain, ('#skF_5'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36853, c_74])).
% 12.39/5.43  tff(c_36860, plain, ('#skF_6'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36853, c_72])).
% 12.39/5.43  tff(c_36845, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_230])).
% 12.39/5.43  tff(c_36874, plain, (k2_zfmisc_1('#skF_5', '#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36853, c_36845])).
% 12.39/5.43  tff(c_50, plain, (![B_27, A_26]: (k1_xboole_0=B_27 | k1_xboole_0=A_26 | k2_zfmisc_1(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.39/5.43  tff(c_37036, plain, (![B_1058, A_1059]: (B_1058='#skF_8' | A_1059='#skF_8' | k2_zfmisc_1(A_1059, B_1058)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36853, c_36853, c_36853, c_50])).
% 12.39/5.43  tff(c_37045, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_36874, c_37036])).
% 12.39/5.43  tff(c_37053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36861, c_36860, c_37045])).
% 12.39/5.43  tff(c_37054, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_36844])).
% 12.39/5.43  tff(c_37062, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_37054, c_72])).
% 12.39/5.43  tff(c_37077, plain, (k2_zfmisc_1('#skF_5', '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_37054, c_36845])).
% 12.39/5.43  tff(c_37239, plain, (![B_1073, A_1074]: (B_1073='#skF_7' | A_1074='#skF_7' | k2_zfmisc_1(A_1074, B_1073)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_37054, c_37054, c_37054, c_50])).
% 12.39/5.43  tff(c_37248, plain, ('#skF_7'='#skF_6' | '#skF_7'='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_37077, c_37239])).
% 12.39/5.43  tff(c_37256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_37062, c_37248])).
% 12.39/5.43  tff(c_37257, plain, ('#skF_6'!='#skF_8'), inference(splitRight, [status(thm)], [c_70])).
% 12.39/5.43  tff(c_37258, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_70])).
% 12.39/5.43  tff(c_37263, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_37258, c_76])).
% 12.39/5.43  tff(c_37553, plain, (![A_1117, C_1118, B_1119]: (r1_tarski(k2_zfmisc_1(A_1117, C_1118), k2_zfmisc_1(B_1119, C_1118)) | ~r1_tarski(A_1117, B_1119))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.39/5.43  tff(c_37573, plain, (![B_1119]: (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_8'), k2_zfmisc_1(B_1119, '#skF_6')) | ~r1_tarski('#skF_5', B_1119))), inference(superposition, [status(thm), theory('equality')], [c_37263, c_37553])).
% 12.39/5.43  tff(c_38828, plain, (![A_1171, B_1172, C_1173]: (~r1_tarski(k2_zfmisc_1(A_1171, B_1172), k2_zfmisc_1(A_1171, C_1173)) | r1_tarski(B_1172, C_1173) | k1_xboole_0=A_1171)), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.39/5.43  tff(c_38847, plain, (r1_tarski('#skF_8', '#skF_6') | k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_37573, c_38828])).
% 12.39/5.43  tff(c_38917, plain, (r1_tarski('#skF_8', '#skF_6') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38847])).
% 12.39/5.43  tff(c_38918, plain, (r1_tarski('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_74, c_38917])).
% 12.39/5.43  tff(c_37576, plain, (![A_1117]: (r1_tarski(k2_zfmisc_1(A_1117, '#skF_6'), k2_zfmisc_1('#skF_5', '#skF_8')) | ~r1_tarski(A_1117, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_37263, c_37553])).
% 12.39/5.43  tff(c_38854, plain, (r1_tarski('#skF_6', '#skF_8') | k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_37576, c_38828])).
% 12.39/5.43  tff(c_38924, plain, (r1_tarski('#skF_6', '#skF_8') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38854])).
% 12.39/5.43  tff(c_38925, plain, (r1_tarski('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_74, c_38924])).
% 12.39/5.43  tff(c_38960, plain, ('#skF_6'='#skF_8' | ~r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_38925, c_40])).
% 12.39/5.43  tff(c_38966, plain, ('#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_38918, c_38960])).
% 12.39/5.43  tff(c_38968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37257, c_38966])).
% 12.39/5.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.39/5.43  
% 12.39/5.43  Inference rules
% 12.39/5.43  ----------------------
% 12.39/5.43  #Ref     : 0
% 12.39/5.43  #Sup     : 9889
% 12.39/5.43  #Fact    : 0
% 12.39/5.43  #Define  : 0
% 12.39/5.43  #Split   : 59
% 12.39/5.43  #Chain   : 0
% 12.39/5.43  #Close   : 0
% 12.39/5.43  
% 12.39/5.43  Ordering : KBO
% 12.39/5.43  
% 12.39/5.43  Simplification rules
% 12.39/5.43  ----------------------
% 12.39/5.43  #Subsume      : 1798
% 12.39/5.43  #Demod        : 6033
% 12.39/5.43  #Tautology    : 3211
% 12.39/5.43  #SimpNegUnit  : 221
% 12.39/5.43  #BackRed      : 259
% 12.39/5.43  
% 12.39/5.43  #Partial instantiations: 0
% 12.39/5.43  #Strategies tried      : 1
% 12.39/5.43  
% 12.39/5.43  Timing (in seconds)
% 12.39/5.43  ----------------------
% 12.39/5.43  Preprocessing        : 0.33
% 12.39/5.43  Parsing              : 0.17
% 12.39/5.43  CNF conversion       : 0.02
% 12.39/5.43  Main loop            : 4.27
% 12.39/5.43  Inferencing          : 0.93
% 12.39/5.43  Reduction            : 1.76
% 12.39/5.43  Demodulation         : 1.36
% 12.39/5.43  BG Simplification    : 0.13
% 12.39/5.43  Subsumption          : 1.17
% 12.39/5.43  Abstraction          : 0.15
% 12.39/5.43  MUC search           : 0.00
% 12.39/5.43  Cooper               : 0.00
% 12.39/5.43  Total                : 4.64
% 12.39/5.43  Index Insertion      : 0.00
% 12.39/5.43  Index Deletion       : 0.00
% 12.39/5.43  Index Matching       : 0.00
% 12.39/5.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
