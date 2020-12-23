%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:17 EST 2020

% Result     : Theorem 9.10s
% Output     : CNFRefutation 9.29s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 469 expanded)
%              Number of leaves         :   22 ( 164 expanded)
%              Depth                    :   17
%              Number of atoms          :  158 ( 933 expanded)
%              Number of equality atoms :   63 ( 454 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(c_40,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_49,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_30,c_54])).

tff(c_38,plain,(
    ! [A_19,C_21,B_20,D_22] : k3_xboole_0(k2_zfmisc_1(A_19,C_21),k2_zfmisc_1(B_20,D_22)) = k2_zfmisc_1(k3_xboole_0(A_19,B_20),k3_xboole_0(C_21,D_22)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12348,plain,(
    ! [A_552,C_553,B_554,D_555] : k3_xboole_0(k2_zfmisc_1(A_552,C_553),k2_zfmisc_1(B_554,D_555)) = k2_zfmisc_1(k3_xboole_0(A_552,B_554),k3_xboole_0(C_553,D_555)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12386,plain,(
    ! [B_554,D_555] : k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_554,D_555)) = k2_zfmisc_1(k3_xboole_0('#skF_6',B_554),k3_xboole_0('#skF_7',D_555)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_12348])).

tff(c_12397,plain,(
    ! [B_554,D_555] : k2_zfmisc_1(k3_xboole_0('#skF_6',B_554),k3_xboole_0('#skF_7',D_555)) = k2_zfmisc_1(k3_xboole_0('#skF_4',B_554),k3_xboole_0('#skF_5',D_555)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12386])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [D_32,A_33,B_34] :
      ( r2_hidden(D_32,A_33)
      | ~ r2_hidden(D_32,k3_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_170,plain,(
    ! [A_54,B_55,B_56] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_54,B_55),B_56),A_54)
      | r1_tarski(k3_xboole_0(A_54,B_55),B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12287,plain,(
    ! [A_546,B_547] : r1_tarski(k3_xboole_0(A_546,B_547),A_546) ),
    inference(resolution,[status(thm)],[c_170,c_4])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12297,plain,(
    ! [A_546,B_547] : k3_xboole_0(k3_xboole_0(A_546,B_547),A_546) = k3_xboole_0(A_546,B_547) ),
    inference(resolution,[status(thm)],[c_12287,c_32])).

tff(c_69,plain,(
    ! [D_29,B_30,A_31] :
      ( r2_hidden(D_29,B_30)
      | ~ r2_hidden(D_29,k3_xboole_0(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12647,plain,(
    ! [A_579,B_580,B_581] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_579,B_580),B_581),B_580)
      | r1_tarski(k3_xboole_0(A_579,B_580),B_581) ) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_12678,plain,(
    ! [A_582,B_583] : r1_tarski(k3_xboole_0(A_582,B_583),B_583) ),
    inference(resolution,[status(thm)],[c_12647,c_4])).

tff(c_12804,plain,(
    ! [A_588,B_589,C_590,D_591] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_588,B_589),k3_xboole_0(C_590,D_591)),k2_zfmisc_1(B_589,D_591)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_12678])).

tff(c_13046,plain,(
    ! [A_605,B_606,C_607,D_608] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_605,B_606),k3_xboole_0(C_607,D_608)),k2_zfmisc_1(A_605,D_608)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12297,c_12804])).

tff(c_13250,plain,(
    ! [B_624,D_625] : r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_4',B_624),k3_xboole_0('#skF_5',D_625)),k2_zfmisc_1('#skF_6',D_625)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12397,c_13046])).

tff(c_13271,plain,(
    ! [D_626] : r1_tarski(k2_zfmisc_1('#skF_4',k3_xboole_0('#skF_5',D_626)),k2_zfmisc_1('#skF_6',D_626)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_13250])).

tff(c_13280,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_13271])).

tff(c_36,plain,(
    ! [B_17,A_16,C_18] :
      ( ~ r1_tarski(k2_zfmisc_1(B_17,A_16),k2_zfmisc_1(C_18,A_16))
      | r1_tarski(B_17,C_18)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_13292,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_13280,c_36])).

tff(c_13301,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_13292])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13305,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_13301,c_26])).

tff(c_13311,plain,(
    ~ r1_tarski('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_13305])).

tff(c_13312,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13301,c_32])).

tff(c_12389,plain,(
    ! [A_552,C_553] : k3_xboole_0(k2_zfmisc_1(A_552,C_553),k2_zfmisc_1('#skF_4','#skF_5')) = k2_zfmisc_1(k3_xboole_0(A_552,'#skF_6'),k3_xboole_0(C_553,'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_12348])).

tff(c_15066,plain,(
    ! [A_683,C_684] : k2_zfmisc_1(k3_xboole_0(A_683,'#skF_6'),k3_xboole_0(C_684,'#skF_7')) = k2_zfmisc_1(k3_xboole_0(A_683,'#skF_4'),k3_xboole_0(C_684,'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12389])).

tff(c_15121,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_6','#skF_4'),k3_xboole_0('#skF_7','#skF_5')) = k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15066,c_12397])).

tff(c_15204,plain,(
    k2_zfmisc_1('#skF_4',k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13312,c_58,c_58,c_12397,c_15121])).

tff(c_12836,plain,(
    ! [B_13,C_590,D_591] : r1_tarski(k2_zfmisc_1(B_13,k3_xboole_0(C_590,D_591)),k2_zfmisc_1(B_13,D_591)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_12804])).

tff(c_15251,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15204,c_12836])).

tff(c_157,plain,(
    ! [B_51,A_52,C_53] :
      ( ~ r1_tarski(k2_zfmisc_1(B_51,A_52),k2_zfmisc_1(C_53,A_52))
      | r1_tarski(B_51,C_53)
      | k1_xboole_0 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_160,plain,(
    ! [C_53] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(C_53,'#skF_7'))
      | r1_tarski('#skF_6',C_53)
      | k1_xboole_0 = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_157])).

tff(c_193,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_196,plain,(
    '#skF_7' != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_42])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_197,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_44])).

tff(c_252,plain,(
    ! [A_61,C_62,B_63,D_64] : k3_xboole_0(k2_zfmisc_1(A_61,C_62),k2_zfmisc_1(B_63,D_64)) = k2_zfmisc_1(k3_xboole_0(A_61,B_63),k3_xboole_0(C_62,D_64)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_290,plain,(
    ! [A_61,C_62] : k3_xboole_0(k2_zfmisc_1(A_61,C_62),k2_zfmisc_1('#skF_4','#skF_5')) = k2_zfmisc_1(k3_xboole_0(A_61,'#skF_6'),k3_xboole_0(C_62,'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_252])).

tff(c_3369,plain,(
    ! [A_228,C_229] : k2_zfmisc_1(k3_xboole_0(A_228,'#skF_6'),k3_xboole_0(C_229,'#skF_7')) = k2_zfmisc_1(k3_xboole_0(A_228,'#skF_4'),k3_xboole_0(C_229,'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_290])).

tff(c_202,plain,(
    ! [A_57,B_58] : r1_tarski(k3_xboole_0(A_57,B_58),A_57) ),
    inference(resolution,[status(thm)],[c_170,c_4])).

tff(c_212,plain,(
    ! [A_57,B_58] : k3_xboole_0(k3_xboole_0(A_57,B_58),A_57) = k3_xboole_0(A_57,B_58) ),
    inference(resolution,[status(thm)],[c_202,c_32])).

tff(c_431,plain,(
    ! [A_81,B_82,B_83] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_81,B_82),B_83),B_82)
      | r1_tarski(k3_xboole_0(A_81,B_82),B_83) ) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_462,plain,(
    ! [A_84,B_85] : r1_tarski(k3_xboole_0(A_84,B_85),B_85) ),
    inference(resolution,[status(thm)],[c_431,c_4])).

tff(c_594,plain,(
    ! [A_93,B_94,C_95,D_96] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_93,B_94),k3_xboole_0(C_95,D_96)),k2_zfmisc_1(B_94,D_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_462])).

tff(c_614,plain,(
    ! [A_57,B_58,C_95,D_96] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_57,B_58),k3_xboole_0(C_95,D_96)),k2_zfmisc_1(A_57,D_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_594])).

tff(c_3489,plain,(
    ! [A_230,C_231] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_230,'#skF_4'),k3_xboole_0(C_231,'#skF_5')),k2_zfmisc_1(A_230,'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3369,c_614])).

tff(c_3526,plain,(
    ! [C_232] : r1_tarski(k2_zfmisc_1('#skF_4',k3_xboole_0(C_232,'#skF_5')),k2_zfmisc_1('#skF_4','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_3489])).

tff(c_34,plain,(
    ! [A_16,B_17,C_18] :
      ( ~ r1_tarski(k2_zfmisc_1(A_16,B_17),k2_zfmisc_1(A_16,C_18))
      | r1_tarski(B_17,C_18)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_195,plain,(
    ! [A_16,B_17,C_18] :
      ( ~ r1_tarski(k2_zfmisc_1(A_16,B_17),k2_zfmisc_1(A_16,C_18))
      | r1_tarski(B_17,C_18)
      | A_16 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_34])).

tff(c_3529,plain,(
    ! [C_232] :
      ( r1_tarski(k3_xboole_0(C_232,'#skF_5'),'#skF_7')
      | '#skF_7' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_3526,c_195])).

tff(c_3553,plain,(
    ! [C_233] : r1_tarski(k3_xboole_0(C_233,'#skF_5'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_3529])).

tff(c_3570,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_3553])).

tff(c_3582,plain,(
    k3_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3570,c_32])).

tff(c_631,plain,(
    ! [A_97,C_98] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_97,'#skF_6'),k3_xboole_0(C_98,'#skF_7')),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_594])).

tff(c_656,plain,(
    ! [C_98] : r1_tarski(k2_zfmisc_1('#skF_6',k3_xboole_0(C_98,'#skF_7')),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_631])).

tff(c_3634,plain,(
    r1_tarski(k2_zfmisc_1('#skF_6','#skF_5'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3582,c_656])).

tff(c_194,plain,(
    ! [B_17,A_16,C_18] :
      ( ~ r1_tarski(k2_zfmisc_1(B_17,A_16),k2_zfmisc_1(C_18,A_16))
      | r1_tarski(B_17,C_18)
      | A_16 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_36])).

tff(c_3880,plain,
    ( r1_tarski('#skF_6','#skF_4')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3634,c_194])).

tff(c_3891,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_3880])).

tff(c_3897,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_3891,c_26])).

tff(c_3903,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_3897])).

tff(c_287,plain,(
    ! [B_63,D_64] : k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(B_63,D_64)) = k2_zfmisc_1(k3_xboole_0('#skF_6',B_63),k3_xboole_0('#skF_7',D_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_252])).

tff(c_3752,plain,(
    ! [B_239,D_240] : k2_zfmisc_1(k3_xboole_0('#skF_6',B_239),k3_xboole_0('#skF_7',D_240)) = k2_zfmisc_1(k3_xboole_0('#skF_4',B_239),k3_xboole_0('#skF_5',D_240)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_287])).

tff(c_3852,plain,(
    ! [B_239] : k2_zfmisc_1(k3_xboole_0('#skF_4',B_239),k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1(k3_xboole_0('#skF_6',B_239),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_3752])).

tff(c_8510,plain,(
    ! [B_384] : k2_zfmisc_1(k3_xboole_0('#skF_6',B_384),'#skF_7') = k2_zfmisc_1(k3_xboole_0('#skF_4',B_384),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3582,c_3852])).

tff(c_8604,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),'#skF_5') = k2_zfmisc_1('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_8510])).

tff(c_8620,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),'#skF_5') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8604])).

tff(c_623,plain,(
    ! [A_93,B_94,B_13] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_93,B_94),B_13),k2_zfmisc_1(B_94,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_594])).

tff(c_8662,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8620,c_623])).

tff(c_8709,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8662,c_194])).

tff(c_8721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_3903,c_8709])).

tff(c_8722,plain,(
    ! [C_53] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1(C_53,'#skF_7'))
      | r1_tarski('#skF_6',C_53) ) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_15317,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_15251,c_8722])).

tff(c_15331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13311,c_15317])).

tff(c_15332,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_15333,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_15338,plain,(
    k2_zfmisc_1('#skF_4','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15333,c_46])).

tff(c_15433,plain,(
    ! [A_710,B_711,C_712] :
      ( ~ r1_tarski(k2_zfmisc_1(A_710,B_711),k2_zfmisc_1(A_710,C_712))
      | r1_tarski(B_711,C_712)
      | k1_xboole_0 = A_710 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_15436,plain,(
    ! [C_712] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4',C_712))
      | r1_tarski('#skF_7',C_712)
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15338,c_15433])).

tff(c_15461,plain,(
    ! [C_716] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4',C_716))
      | r1_tarski('#skF_7',C_716) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_15436])).

tff(c_15471,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_15461])).

tff(c_15473,plain,
    ( '#skF_7' = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_15471,c_26])).

tff(c_15479,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_15332,c_15473])).

tff(c_15439,plain,(
    ! [B_711] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4',B_711),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_711,'#skF_7')
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15338,c_15433])).

tff(c_15481,plain,(
    ! [B_717] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4',B_717),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_717,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_15439])).

tff(c_15488,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_15481])).

tff(c_15494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15479,c_15488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:33:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.10/3.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.19/3.23  
% 9.19/3.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.19/3.24  %$ r2_hidden > r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 9.19/3.24  
% 9.19/3.24  %Foreground sorts:
% 9.19/3.24  
% 9.19/3.24  
% 9.19/3.24  %Background operators:
% 9.19/3.24  
% 9.19/3.24  
% 9.19/3.24  %Foreground operators:
% 9.19/3.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.19/3.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.19/3.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.19/3.24  tff('#skF_7', type, '#skF_7': $i).
% 9.19/3.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.19/3.24  tff('#skF_5', type, '#skF_5': $i).
% 9.19/3.24  tff('#skF_6', type, '#skF_6': $i).
% 9.19/3.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.19/3.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.19/3.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.19/3.24  tff('#skF_4', type, '#skF_4': $i).
% 9.19/3.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.19/3.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.19/3.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.19/3.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.19/3.24  
% 9.29/3.26  tff(f_75, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 9.29/3.26  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.29/3.26  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.29/3.26  tff(f_64, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 9.29/3.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.29/3.26  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.29/3.26  tff(f_62, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 9.29/3.26  tff(c_40, plain, ('#skF_7'!='#skF_5' | '#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.29/3.26  tff(c_49, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_40])).
% 9.29/3.26  tff(c_42, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.29/3.26  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.29/3.26  tff(c_54, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.29/3.26  tff(c_58, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_30, c_54])).
% 9.29/3.26  tff(c_38, plain, (![A_19, C_21, B_20, D_22]: (k3_xboole_0(k2_zfmisc_1(A_19, C_21), k2_zfmisc_1(B_20, D_22))=k2_zfmisc_1(k3_xboole_0(A_19, B_20), k3_xboole_0(C_21, D_22)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.29/3.26  tff(c_46, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.29/3.26  tff(c_12348, plain, (![A_552, C_553, B_554, D_555]: (k3_xboole_0(k2_zfmisc_1(A_552, C_553), k2_zfmisc_1(B_554, D_555))=k2_zfmisc_1(k3_xboole_0(A_552, B_554), k3_xboole_0(C_553, D_555)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.29/3.26  tff(c_12386, plain, (![B_554, D_555]: (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_554, D_555))=k2_zfmisc_1(k3_xboole_0('#skF_6', B_554), k3_xboole_0('#skF_7', D_555)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_12348])).
% 9.29/3.26  tff(c_12397, plain, (![B_554, D_555]: (k2_zfmisc_1(k3_xboole_0('#skF_6', B_554), k3_xboole_0('#skF_7', D_555))=k2_zfmisc_1(k3_xboole_0('#skF_4', B_554), k3_xboole_0('#skF_5', D_555)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12386])).
% 9.29/3.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.29/3.26  tff(c_78, plain, (![D_32, A_33, B_34]: (r2_hidden(D_32, A_33) | ~r2_hidden(D_32, k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.29/3.26  tff(c_170, plain, (![A_54, B_55, B_56]: (r2_hidden('#skF_1'(k3_xboole_0(A_54, B_55), B_56), A_54) | r1_tarski(k3_xboole_0(A_54, B_55), B_56))), inference(resolution, [status(thm)], [c_6, c_78])).
% 9.29/3.26  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.29/3.26  tff(c_12287, plain, (![A_546, B_547]: (r1_tarski(k3_xboole_0(A_546, B_547), A_546))), inference(resolution, [status(thm)], [c_170, c_4])).
% 9.29/3.26  tff(c_32, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.29/3.26  tff(c_12297, plain, (![A_546, B_547]: (k3_xboole_0(k3_xboole_0(A_546, B_547), A_546)=k3_xboole_0(A_546, B_547))), inference(resolution, [status(thm)], [c_12287, c_32])).
% 9.29/3.26  tff(c_69, plain, (![D_29, B_30, A_31]: (r2_hidden(D_29, B_30) | ~r2_hidden(D_29, k3_xboole_0(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.29/3.26  tff(c_12647, plain, (![A_579, B_580, B_581]: (r2_hidden('#skF_1'(k3_xboole_0(A_579, B_580), B_581), B_580) | r1_tarski(k3_xboole_0(A_579, B_580), B_581))), inference(resolution, [status(thm)], [c_6, c_69])).
% 9.29/3.26  tff(c_12678, plain, (![A_582, B_583]: (r1_tarski(k3_xboole_0(A_582, B_583), B_583))), inference(resolution, [status(thm)], [c_12647, c_4])).
% 9.29/3.26  tff(c_12804, plain, (![A_588, B_589, C_590, D_591]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_588, B_589), k3_xboole_0(C_590, D_591)), k2_zfmisc_1(B_589, D_591)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_12678])).
% 9.29/3.26  tff(c_13046, plain, (![A_605, B_606, C_607, D_608]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_605, B_606), k3_xboole_0(C_607, D_608)), k2_zfmisc_1(A_605, D_608)))), inference(superposition, [status(thm), theory('equality')], [c_12297, c_12804])).
% 9.29/3.26  tff(c_13250, plain, (![B_624, D_625]: (r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_4', B_624), k3_xboole_0('#skF_5', D_625)), k2_zfmisc_1('#skF_6', D_625)))), inference(superposition, [status(thm), theory('equality')], [c_12397, c_13046])).
% 9.29/3.26  tff(c_13271, plain, (![D_626]: (r1_tarski(k2_zfmisc_1('#skF_4', k3_xboole_0('#skF_5', D_626)), k2_zfmisc_1('#skF_6', D_626)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_13250])).
% 9.29/3.26  tff(c_13280, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_13271])).
% 9.29/3.26  tff(c_36, plain, (![B_17, A_16, C_18]: (~r1_tarski(k2_zfmisc_1(B_17, A_16), k2_zfmisc_1(C_18, A_16)) | r1_tarski(B_17, C_18) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.29/3.26  tff(c_13292, plain, (r1_tarski('#skF_4', '#skF_6') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_13280, c_36])).
% 9.29/3.26  tff(c_13301, plain, (r1_tarski('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_42, c_13292])).
% 9.29/3.26  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.29/3.26  tff(c_13305, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_13301, c_26])).
% 9.29/3.26  tff(c_13311, plain, (~r1_tarski('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_49, c_13305])).
% 9.29/3.26  tff(c_13312, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_13301, c_32])).
% 9.29/3.26  tff(c_12389, plain, (![A_552, C_553]: (k3_xboole_0(k2_zfmisc_1(A_552, C_553), k2_zfmisc_1('#skF_4', '#skF_5'))=k2_zfmisc_1(k3_xboole_0(A_552, '#skF_6'), k3_xboole_0(C_553, '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_12348])).
% 9.29/3.26  tff(c_15066, plain, (![A_683, C_684]: (k2_zfmisc_1(k3_xboole_0(A_683, '#skF_6'), k3_xboole_0(C_684, '#skF_7'))=k2_zfmisc_1(k3_xboole_0(A_683, '#skF_4'), k3_xboole_0(C_684, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12389])).
% 9.29/3.26  tff(c_15121, plain, (k2_zfmisc_1(k3_xboole_0('#skF_6', '#skF_4'), k3_xboole_0('#skF_7', '#skF_5'))=k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_15066, c_12397])).
% 9.29/3.26  tff(c_15204, plain, (k2_zfmisc_1('#skF_4', k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13312, c_58, c_58, c_12397, c_15121])).
% 9.29/3.26  tff(c_12836, plain, (![B_13, C_590, D_591]: (r1_tarski(k2_zfmisc_1(B_13, k3_xboole_0(C_590, D_591)), k2_zfmisc_1(B_13, D_591)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_12804])).
% 9.29/3.26  tff(c_15251, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_15204, c_12836])).
% 9.29/3.26  tff(c_157, plain, (![B_51, A_52, C_53]: (~r1_tarski(k2_zfmisc_1(B_51, A_52), k2_zfmisc_1(C_53, A_52)) | r1_tarski(B_51, C_53) | k1_xboole_0=A_52)), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.29/3.26  tff(c_160, plain, (![C_53]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(C_53, '#skF_7')) | r1_tarski('#skF_6', C_53) | k1_xboole_0='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_46, c_157])).
% 9.29/3.26  tff(c_193, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_160])).
% 9.29/3.26  tff(c_196, plain, ('#skF_7'!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_42])).
% 9.29/3.26  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.29/3.26  tff(c_197, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_44])).
% 9.29/3.26  tff(c_252, plain, (![A_61, C_62, B_63, D_64]: (k3_xboole_0(k2_zfmisc_1(A_61, C_62), k2_zfmisc_1(B_63, D_64))=k2_zfmisc_1(k3_xboole_0(A_61, B_63), k3_xboole_0(C_62, D_64)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.29/3.26  tff(c_290, plain, (![A_61, C_62]: (k3_xboole_0(k2_zfmisc_1(A_61, C_62), k2_zfmisc_1('#skF_4', '#skF_5'))=k2_zfmisc_1(k3_xboole_0(A_61, '#skF_6'), k3_xboole_0(C_62, '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_252])).
% 9.29/3.26  tff(c_3369, plain, (![A_228, C_229]: (k2_zfmisc_1(k3_xboole_0(A_228, '#skF_6'), k3_xboole_0(C_229, '#skF_7'))=k2_zfmisc_1(k3_xboole_0(A_228, '#skF_4'), k3_xboole_0(C_229, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_290])).
% 9.29/3.26  tff(c_202, plain, (![A_57, B_58]: (r1_tarski(k3_xboole_0(A_57, B_58), A_57))), inference(resolution, [status(thm)], [c_170, c_4])).
% 9.29/3.26  tff(c_212, plain, (![A_57, B_58]: (k3_xboole_0(k3_xboole_0(A_57, B_58), A_57)=k3_xboole_0(A_57, B_58))), inference(resolution, [status(thm)], [c_202, c_32])).
% 9.29/3.26  tff(c_431, plain, (![A_81, B_82, B_83]: (r2_hidden('#skF_1'(k3_xboole_0(A_81, B_82), B_83), B_82) | r1_tarski(k3_xboole_0(A_81, B_82), B_83))), inference(resolution, [status(thm)], [c_6, c_69])).
% 9.29/3.26  tff(c_462, plain, (![A_84, B_85]: (r1_tarski(k3_xboole_0(A_84, B_85), B_85))), inference(resolution, [status(thm)], [c_431, c_4])).
% 9.29/3.26  tff(c_594, plain, (![A_93, B_94, C_95, D_96]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_93, B_94), k3_xboole_0(C_95, D_96)), k2_zfmisc_1(B_94, D_96)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_462])).
% 9.29/3.26  tff(c_614, plain, (![A_57, B_58, C_95, D_96]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_57, B_58), k3_xboole_0(C_95, D_96)), k2_zfmisc_1(A_57, D_96)))), inference(superposition, [status(thm), theory('equality')], [c_212, c_594])).
% 9.29/3.26  tff(c_3489, plain, (![A_230, C_231]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_230, '#skF_4'), k3_xboole_0(C_231, '#skF_5')), k2_zfmisc_1(A_230, '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_3369, c_614])).
% 9.29/3.26  tff(c_3526, plain, (![C_232]: (r1_tarski(k2_zfmisc_1('#skF_4', k3_xboole_0(C_232, '#skF_5')), k2_zfmisc_1('#skF_4', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_58, c_3489])).
% 9.29/3.26  tff(c_34, plain, (![A_16, B_17, C_18]: (~r1_tarski(k2_zfmisc_1(A_16, B_17), k2_zfmisc_1(A_16, C_18)) | r1_tarski(B_17, C_18) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.29/3.26  tff(c_195, plain, (![A_16, B_17, C_18]: (~r1_tarski(k2_zfmisc_1(A_16, B_17), k2_zfmisc_1(A_16, C_18)) | r1_tarski(B_17, C_18) | A_16='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_34])).
% 9.29/3.26  tff(c_3529, plain, (![C_232]: (r1_tarski(k3_xboole_0(C_232, '#skF_5'), '#skF_7') | '#skF_7'='#skF_4')), inference(resolution, [status(thm)], [c_3526, c_195])).
% 9.29/3.26  tff(c_3553, plain, (![C_233]: (r1_tarski(k3_xboole_0(C_233, '#skF_5'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_197, c_3529])).
% 9.29/3.26  tff(c_3570, plain, (r1_tarski('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_58, c_3553])).
% 9.29/3.26  tff(c_3582, plain, (k3_xboole_0('#skF_5', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_3570, c_32])).
% 9.29/3.26  tff(c_631, plain, (![A_97, C_98]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_97, '#skF_6'), k3_xboole_0(C_98, '#skF_7')), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_594])).
% 9.29/3.26  tff(c_656, plain, (![C_98]: (r1_tarski(k2_zfmisc_1('#skF_6', k3_xboole_0(C_98, '#skF_7')), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_58, c_631])).
% 9.29/3.26  tff(c_3634, plain, (r1_tarski(k2_zfmisc_1('#skF_6', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3582, c_656])).
% 9.29/3.26  tff(c_194, plain, (![B_17, A_16, C_18]: (~r1_tarski(k2_zfmisc_1(B_17, A_16), k2_zfmisc_1(C_18, A_16)) | r1_tarski(B_17, C_18) | A_16='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_36])).
% 9.29/3.26  tff(c_3880, plain, (r1_tarski('#skF_6', '#skF_4') | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_3634, c_194])).
% 9.29/3.26  tff(c_3891, plain, (r1_tarski('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_196, c_3880])).
% 9.29/3.26  tff(c_3897, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_3891, c_26])).
% 9.29/3.26  tff(c_3903, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_49, c_3897])).
% 9.29/3.26  tff(c_287, plain, (![B_63, D_64]: (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(B_63, D_64))=k2_zfmisc_1(k3_xboole_0('#skF_6', B_63), k3_xboole_0('#skF_7', D_64)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_252])).
% 9.29/3.26  tff(c_3752, plain, (![B_239, D_240]: (k2_zfmisc_1(k3_xboole_0('#skF_6', B_239), k3_xboole_0('#skF_7', D_240))=k2_zfmisc_1(k3_xboole_0('#skF_4', B_239), k3_xboole_0('#skF_5', D_240)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_287])).
% 9.29/3.26  tff(c_3852, plain, (![B_239]: (k2_zfmisc_1(k3_xboole_0('#skF_4', B_239), k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1(k3_xboole_0('#skF_6', B_239), '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_3752])).
% 9.29/3.26  tff(c_8510, plain, (![B_384]: (k2_zfmisc_1(k3_xboole_0('#skF_6', B_384), '#skF_7')=k2_zfmisc_1(k3_xboole_0('#skF_4', B_384), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3582, c_3852])).
% 9.29/3.26  tff(c_8604, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), '#skF_5')=k2_zfmisc_1('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_58, c_8510])).
% 9.29/3.26  tff(c_8620, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8604])).
% 9.29/3.26  tff(c_623, plain, (![A_93, B_94, B_13]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_93, B_94), B_13), k2_zfmisc_1(B_94, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_594])).
% 9.29/3.26  tff(c_8662, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8620, c_623])).
% 9.29/3.26  tff(c_8709, plain, (r1_tarski('#skF_4', '#skF_6') | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_8662, c_194])).
% 9.29/3.26  tff(c_8721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_3903, c_8709])).
% 9.29/3.26  tff(c_8722, plain, (![C_53]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1(C_53, '#skF_7')) | r1_tarski('#skF_6', C_53))), inference(splitRight, [status(thm)], [c_160])).
% 9.29/3.26  tff(c_15317, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_15251, c_8722])).
% 9.29/3.26  tff(c_15331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13311, c_15317])).
% 9.29/3.26  tff(c_15332, plain, ('#skF_7'!='#skF_5'), inference(splitRight, [status(thm)], [c_40])).
% 9.29/3.26  tff(c_15333, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 9.29/3.26  tff(c_15338, plain, (k2_zfmisc_1('#skF_4', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15333, c_46])).
% 9.29/3.26  tff(c_15433, plain, (![A_710, B_711, C_712]: (~r1_tarski(k2_zfmisc_1(A_710, B_711), k2_zfmisc_1(A_710, C_712)) | r1_tarski(B_711, C_712) | k1_xboole_0=A_710)), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.29/3.26  tff(c_15436, plain, (![C_712]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', C_712)) | r1_tarski('#skF_7', C_712) | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_15338, c_15433])).
% 9.29/3.26  tff(c_15461, plain, (![C_716]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', C_716)) | r1_tarski('#skF_7', C_716))), inference(negUnitSimplification, [status(thm)], [c_44, c_15436])).
% 9.29/3.26  tff(c_15471, plain, (r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_15461])).
% 9.29/3.26  tff(c_15473, plain, ('#skF_7'='#skF_5' | ~r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_15471, c_26])).
% 9.29/3.26  tff(c_15479, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_15332, c_15473])).
% 9.29/3.26  tff(c_15439, plain, (![B_711]: (~r1_tarski(k2_zfmisc_1('#skF_4', B_711), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_711, '#skF_7') | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_15338, c_15433])).
% 9.29/3.26  tff(c_15481, plain, (![B_717]: (~r1_tarski(k2_zfmisc_1('#skF_4', B_717), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_717, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_44, c_15439])).
% 9.29/3.26  tff(c_15488, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_30, c_15481])).
% 9.29/3.26  tff(c_15494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15479, c_15488])).
% 9.29/3.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.29/3.26  
% 9.29/3.26  Inference rules
% 9.29/3.26  ----------------------
% 9.29/3.26  #Ref     : 0
% 9.29/3.26  #Sup     : 3825
% 9.29/3.26  #Fact    : 0
% 9.29/3.26  #Define  : 0
% 9.29/3.26  #Split   : 6
% 9.29/3.26  #Chain   : 0
% 9.29/3.26  #Close   : 0
% 9.29/3.26  
% 9.29/3.26  Ordering : KBO
% 9.29/3.26  
% 9.29/3.26  Simplification rules
% 9.29/3.26  ----------------------
% 9.29/3.26  #Subsume      : 290
% 9.29/3.26  #Demod        : 2055
% 9.29/3.26  #Tautology    : 1432
% 9.29/3.26  #SimpNegUnit  : 61
% 9.29/3.26  #BackRed      : 39
% 9.29/3.26  
% 9.29/3.26  #Partial instantiations: 0
% 9.29/3.26  #Strategies tried      : 1
% 9.29/3.26  
% 9.29/3.26  Timing (in seconds)
% 9.29/3.26  ----------------------
% 9.29/3.26  Preprocessing        : 0.31
% 9.29/3.26  Parsing              : 0.16
% 9.29/3.26  CNF conversion       : 0.02
% 9.29/3.26  Main loop            : 2.18
% 9.29/3.26  Inferencing          : 0.60
% 9.29/3.26  Reduction            : 0.85
% 9.29/3.26  Demodulation         : 0.67
% 9.29/3.26  BG Simplification    : 0.07
% 9.29/3.26  Subsumption          : 0.51
% 9.29/3.26  Abstraction          : 0.09
% 9.29/3.26  MUC search           : 0.00
% 9.29/3.26  Cooper               : 0.00
% 9.29/3.26  Total                : 2.53
% 9.29/3.26  Index Insertion      : 0.00
% 9.29/3.26  Index Deletion       : 0.00
% 9.29/3.26  Index Matching       : 0.00
% 9.29/3.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
