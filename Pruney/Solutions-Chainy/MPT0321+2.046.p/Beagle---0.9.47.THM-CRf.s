%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:19 EST 2020

% Result     : Theorem 8.24s
% Output     : CNFRefutation 8.65s
% Verified   : 
% Statistics : Number of formulae       :  186 (2250 expanded)
%              Number of leaves         :   19 ( 678 expanded)
%              Depth                    :   21
%              Number of atoms          :  317 (6133 expanded)
%              Number of equality atoms :   98 (2267 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_28,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_35,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_384,plain,(
    ! [A_67,B_68,C_69] :
      ( r2_hidden('#skF_1'(A_67,B_68,C_69),B_68)
      | r2_hidden('#skF_2'(A_67,B_68,C_69),C_69)
      | k3_xboole_0(A_67,B_68) = C_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    k2_zfmisc_1('#skF_6','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_94,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( r2_hidden(k4_tarski(A_39,B_40),k2_zfmisc_1(C_41,D_42))
      | ~ r2_hidden(B_40,D_42)
      | ~ r2_hidden(A_39,C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_138,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(k4_tarski(A_45,B_46),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_46,'#skF_7')
      | ~ r2_hidden(A_45,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_94])).

tff(c_26,plain,(
    ! [A_9,C_11,B_10,D_12] :
      ( r2_hidden(A_9,C_11)
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_152,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,'#skF_4')
      | ~ r2_hidden(B_46,'#skF_7')
      | ~ r2_hidden(A_45,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_138,c_26])).

tff(c_180,plain,(
    ! [B_49] : ~ r2_hidden(B_49,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_195,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_20,c_180])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_210,plain,(
    '#skF_7' != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_30])).

tff(c_269,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_3'(A_58),A_58)
      | A_58 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_20])).

tff(c_177,plain,(
    ! [B_46] : ~ r2_hidden(B_46,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,(
    ! [B_20,D_21,A_22,C_23] :
      ( r2_hidden(B_20,D_21)
      | ~ r2_hidden(k4_tarski(A_22,B_20),k2_zfmisc_1(C_23,D_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_56,plain,(
    ! [B_20,A_22] :
      ( r2_hidden(B_20,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_22,B_20),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_53])).

tff(c_114,plain,(
    ! [B_40,A_39] :
      ( r2_hidden(B_40,'#skF_7')
      | ~ r2_hidden(B_40,'#skF_5')
      | ~ r2_hidden(A_39,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_94,c_56])).

tff(c_156,plain,(
    ! [A_47] : ~ r2_hidden(A_47,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_168,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_156])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_168])).

tff(c_175,plain,(
    ! [B_40] :
      ( r2_hidden(B_40,'#skF_7')
      | ~ r2_hidden(B_40,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_178,plain,(
    ! [B_40] : ~ r2_hidden(B_40,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_175])).

tff(c_273,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_269,c_178])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_273])).

tff(c_290,plain,(
    ! [A_45] :
      ( r2_hidden(A_45,'#skF_4')
      | ~ r2_hidden(A_45,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_1707,plain,(
    ! [A_199,C_200] :
      ( r2_hidden('#skF_1'(A_199,'#skF_6',C_200),'#skF_4')
      | r2_hidden('#skF_2'(A_199,'#skF_6',C_200),C_200)
      | k3_xboole_0(A_199,'#skF_6') = C_200 ) ),
    inference(resolution,[status(thm)],[c_384,c_290])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1737,plain,(
    ! [A_199] :
      ( r2_hidden('#skF_2'(A_199,'#skF_6','#skF_4'),'#skF_4')
      | k3_xboole_0(A_199,'#skF_6') = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1707,c_14])).

tff(c_58,plain,(
    ! [A_26,C_27,B_28,D_29] :
      ( r2_hidden(A_26,C_27)
      | ~ r2_hidden(k4_tarski(A_26,B_28),k2_zfmisc_1(C_27,D_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_61,plain,(
    ! [A_26,B_28] :
      ( r2_hidden(A_26,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_26,B_28),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_58])).

tff(c_112,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(A_39,'#skF_6')
      | ~ r2_hidden(B_40,'#skF_5')
      | ~ r2_hidden(A_39,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_94,c_61])).

tff(c_117,plain,(
    ! [B_43] : ~ r2_hidden(B_43,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_129,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_117])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_129])).

tff(c_136,plain,(
    ! [A_39] :
      ( r2_hidden(A_39,'#skF_6')
      | ~ r2_hidden(A_39,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_291,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r2_hidden('#skF_1'(A_59,B_60,C_61),C_61)
      | r2_hidden('#skF_2'(A_59,B_60,C_61),C_61)
      | k3_xboole_0(A_59,B_60) = C_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1222,plain,(
    ! [A_154,B_155] :
      ( r2_hidden('#skF_2'(A_154,B_155,'#skF_6'),'#skF_6')
      | k3_xboole_0(A_154,B_155) = '#skF_6'
      | ~ r2_hidden('#skF_1'(A_154,B_155,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_136,c_291])).

tff(c_1252,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_4',B_2,'#skF_6'),'#skF_6')
      | k3_xboole_0('#skF_4',B_2) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_18,c_1222])).

tff(c_476,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_2'(A_72,B_73,B_73),B_73)
      | k3_xboole_0(A_72,B_73) = B_73 ) ),
    inference(resolution,[status(thm)],[c_384,c_14])).

tff(c_494,plain,(
    ! [A_72] :
      ( r2_hidden('#skF_2'(A_72,'#skF_6','#skF_6'),'#skF_4')
      | k3_xboole_0(A_72,'#skF_6') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_476,c_290])).

tff(c_800,plain,(
    ! [A_119,B_120,C_121] :
      ( r2_hidden('#skF_1'(A_119,B_120,C_121),B_120)
      | ~ r2_hidden('#skF_2'(A_119,B_120,C_121),B_120)
      | ~ r2_hidden('#skF_2'(A_119,B_120,C_121),A_119)
      | k3_xboole_0(A_119,B_120) = C_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_830,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_6','#skF_6'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_6'),'#skF_6')
    | k3_xboole_0('#skF_4','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_494,c_800])).

tff(c_2072,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_830])).

tff(c_2086,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1252,c_2072])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1144,plain,(
    ! [C_148,B_149] :
      ( ~ r2_hidden('#skF_2'(C_148,B_149,C_148),B_149)
      | r2_hidden('#skF_1'(C_148,B_149,C_148),B_149)
      | k3_xboole_0(C_148,B_149) = C_148 ) ),
    inference(resolution,[status(thm)],[c_16,c_800])).

tff(c_1212,plain,(
    ! [C_153] :
      ( r2_hidden('#skF_1'(C_153,'#skF_6',C_153),'#skF_4')
      | ~ r2_hidden('#skF_2'(C_153,'#skF_6',C_153),'#skF_6')
      | k3_xboole_0(C_153,'#skF_6') = C_153 ) ),
    inference(resolution,[status(thm)],[c_1144,c_290])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1220,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_6')
    | k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1212,c_8])).

tff(c_3879,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_6')
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2086,c_1220])).

tff(c_3880,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_3879])).

tff(c_3881,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3880])).

tff(c_3885,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_3881])).

tff(c_3896,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1737,c_3885])).

tff(c_3898,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3896,c_2086])).

tff(c_3900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_3898])).

tff(c_3901,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3880])).

tff(c_3913,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1737,c_3901])).

tff(c_3998,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3913,c_2086])).

tff(c_4000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_3998])).

tff(c_4002,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_830])).

tff(c_4009,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4002,c_290])).

tff(c_4001,plain,
    ( k3_xboole_0('#skF_4','#skF_6') = '#skF_6'
    | r2_hidden('#skF_1'('#skF_4','#skF_6','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_830])).

tff(c_4043,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_6','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4001])).

tff(c_4045,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_6'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_6'),'#skF_4')
    | k3_xboole_0('#skF_4','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4043,c_8])).

tff(c_4054,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4009,c_4002,c_4045])).

tff(c_4368,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_6')
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_1220])).

tff(c_4369,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_4368])).

tff(c_4370,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4369])).

tff(c_4374,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_4370])).

tff(c_4385,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1737,c_4374])).

tff(c_4387,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4385,c_4054])).

tff(c_4389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_4387])).

tff(c_4390,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4369])).

tff(c_4488,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1737,c_4390])).

tff(c_4490,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4488,c_4054])).

tff(c_4492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_4490])).

tff(c_4493,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4001])).

tff(c_6174,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_6')
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4493,c_1220])).

tff(c_6175,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_6174])).

tff(c_6176,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6175])).

tff(c_6221,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_6176])).

tff(c_6232,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1737,c_6221])).

tff(c_6234,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6232,c_4493])).

tff(c_6236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_6234])).

tff(c_6237,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_6','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_6175])).

tff(c_6249,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1737,c_6237])).

tff(c_6251,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6249,c_4493])).

tff(c_6253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_6251])).

tff(c_6254,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_6643,plain,(
    ! [A_534,B_535,C_536] :
      ( r2_hidden('#skF_1'(A_534,B_535,C_536),A_534)
      | r2_hidden('#skF_2'(A_534,B_535,C_536),C_536)
      | k3_xboole_0(A_534,B_535) = C_536 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6255,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_6261,plain,(
    k2_zfmisc_1('#skF_4','#skF_7') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6255,c_34])).

tff(c_6318,plain,(
    ! [A_489,B_490,C_491,D_492] :
      ( r2_hidden(k4_tarski(A_489,B_490),k2_zfmisc_1(C_491,D_492))
      | ~ r2_hidden(B_490,D_492)
      | ~ r2_hidden(A_489,C_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6385,plain,(
    ! [A_498,B_499] :
      ( r2_hidden(k4_tarski(A_498,B_499),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_499,'#skF_7')
      | ~ r2_hidden(A_498,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6261,c_6318])).

tff(c_24,plain,(
    ! [B_10,D_12,A_9,C_11] :
      ( r2_hidden(B_10,D_12)
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6397,plain,(
    ! [B_499,A_498] :
      ( r2_hidden(B_499,'#skF_5')
      | ~ r2_hidden(B_499,'#skF_7')
      | ~ r2_hidden(A_498,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6385,c_24])).

tff(c_6399,plain,(
    ! [A_500] : ~ r2_hidden(A_500,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6397])).

tff(c_6411,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_6399])).

tff(c_6417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6411])).

tff(c_6418,plain,(
    ! [B_499] :
      ( r2_hidden(B_499,'#skF_5')
      | ~ r2_hidden(B_499,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_6397])).

tff(c_6806,plain,(
    ! [B_559,C_560] :
      ( r2_hidden('#skF_1'('#skF_7',B_559,C_560),'#skF_5')
      | r2_hidden('#skF_2'('#skF_7',B_559,C_560),C_560)
      | k3_xboole_0('#skF_7',B_559) = C_560 ) ),
    inference(resolution,[status(thm)],[c_6643,c_6418])).

tff(c_6829,plain,(
    ! [B_559] :
      ( r2_hidden('#skF_2'('#skF_7',B_559,'#skF_5'),'#skF_5')
      | k3_xboole_0('#skF_7',B_559) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_6806,c_14])).

tff(c_6278,plain,(
    ! [B_472,D_473,A_474,C_475] :
      ( r2_hidden(B_472,D_473)
      | ~ r2_hidden(k4_tarski(A_474,B_472),k2_zfmisc_1(C_475,D_473)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6281,plain,(
    ! [B_472,A_474] :
      ( r2_hidden(B_472,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_474,B_472),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6261,c_6278])).

tff(c_6332,plain,(
    ! [B_490,A_489] :
      ( r2_hidden(B_490,'#skF_7')
      | ~ r2_hidden(B_490,'#skF_5')
      | ~ r2_hidden(A_489,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6318,c_6281])).

tff(c_6357,plain,(
    ! [A_496] : ~ r2_hidden(A_496,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6332])).

tff(c_6375,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_6357])).

tff(c_6382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6375])).

tff(c_6383,plain,(
    ! [B_490] :
      ( r2_hidden(B_490,'#skF_7')
      | ~ r2_hidden(B_490,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_6332])).

tff(c_6707,plain,(
    ! [A_548,B_549,C_550] :
      ( r2_hidden('#skF_1'(A_548,B_549,C_550),A_548)
      | ~ r2_hidden('#skF_2'(A_548,B_549,C_550),B_549)
      | ~ r2_hidden('#skF_2'(A_548,B_549,C_550),A_548)
      | k3_xboole_0(A_548,B_549) = C_550 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6744,plain,(
    ! [A_553,C_554] :
      ( ~ r2_hidden('#skF_2'(A_553,C_554,C_554),A_553)
      | r2_hidden('#skF_1'(A_553,C_554,C_554),A_553)
      | k3_xboole_0(A_553,C_554) = C_554 ) ),
    inference(resolution,[status(thm)],[c_18,c_6707])).

tff(c_6767,plain,(
    ! [C_554] :
      ( r2_hidden('#skF_1'('#skF_7',C_554,C_554),'#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_7',C_554,C_554),'#skF_7')
      | k3_xboole_0('#skF_7',C_554) = C_554 ) ),
    inference(resolution,[status(thm)],[c_6744,c_6418])).

tff(c_6838,plain,(
    ! [A_562,B_563,C_564] :
      ( ~ r2_hidden('#skF_1'(A_562,B_563,C_564),C_564)
      | ~ r2_hidden('#skF_2'(A_562,B_563,C_564),B_563)
      | ~ r2_hidden('#skF_2'(A_562,B_563,C_564),A_562)
      | k3_xboole_0(A_562,B_563) = C_564 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6865,plain,
    ( ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_5'),'#skF_7')
    | k3_xboole_0('#skF_7','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6767,c_6838])).

tff(c_7015,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_6865])).

tff(c_7019,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6383,c_7015])).

tff(c_7029,plain,(
    k3_xboole_0('#skF_7','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6829,c_7019])).

tff(c_6681,plain,(
    ! [A_537,B_538] :
      ( r2_hidden('#skF_2'(A_537,B_538,A_537),A_537)
      | k3_xboole_0(A_537,B_538) = A_537 ) ),
    inference(resolution,[status(thm)],[c_6643,c_14])).

tff(c_6694,plain,(
    ! [B_538] :
      ( r2_hidden('#skF_2'('#skF_7',B_538,'#skF_7'),'#skF_5')
      | k3_xboole_0('#skF_7',B_538) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_6681,c_6418])).

tff(c_6531,plain,(
    ! [A_517,B_518,C_519] :
      ( r2_hidden('#skF_1'(A_517,B_518,C_519),B_518)
      | r2_hidden('#skF_2'(A_517,B_518,C_519),C_519)
      | k3_xboole_0(A_517,B_518) = C_519 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6449,plain,(
    ! [A_502,B_503,C_504] :
      ( ~ r2_hidden('#skF_1'(A_502,B_503,C_504),C_504)
      | r2_hidden('#skF_2'(A_502,B_503,C_504),C_504)
      | k3_xboole_0(A_502,B_503) = C_504 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6458,plain,(
    ! [A_502,B_503] :
      ( r2_hidden('#skF_2'(A_502,B_503,'#skF_7'),'#skF_7')
      | k3_xboole_0(A_502,B_503) = '#skF_7'
      | ~ r2_hidden('#skF_1'(A_502,B_503,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6383,c_6449])).

tff(c_6562,plain,(
    ! [A_517] :
      ( r2_hidden('#skF_2'(A_517,'#skF_5','#skF_7'),'#skF_7')
      | k3_xboole_0(A_517,'#skF_5') = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_6531,c_6458])).

tff(c_7084,plain,(
    ! [A_567,B_568,C_569] :
      ( r2_hidden('#skF_1'(A_567,B_568,C_569),B_568)
      | ~ r2_hidden('#skF_2'(A_567,B_568,C_569),B_568)
      | ~ r2_hidden('#skF_2'(A_567,B_568,C_569),A_567)
      | k3_xboole_0(A_567,B_568) = C_569 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7102,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_5','#skF_7'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_5')
    | k3_xboole_0('#skF_7','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6562,c_7084])).

tff(c_7126,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_5','#skF_7'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_5')
    | '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7029,c_7102])).

tff(c_7127,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_5','#skF_7'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_6254,c_7126])).

tff(c_7237,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7127])).

tff(c_7240,plain,(
    k3_xboole_0('#skF_7','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6694,c_7237])).

tff(c_7245,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7029,c_7240])).

tff(c_7247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6254,c_7245])).

tff(c_7248,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_5','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_7127])).

tff(c_7252,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | k3_xboole_0('#skF_7','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_7248,c_6458])).

tff(c_7254,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7029,c_7252])).

tff(c_7255,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_6254,c_7254])).

tff(c_7249,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_7127])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7257,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | k3_xboole_0('#skF_7','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_7249,c_12])).

tff(c_7259,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7029,c_7257])).

tff(c_7260,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_6254,c_7259])).

tff(c_7273,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_5','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7255,c_7260])).

tff(c_7275,plain,
    ( ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | k3_xboole_0('#skF_7','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_7273,c_8])).

tff(c_7284,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7029,c_7255,c_7249,c_7275])).

tff(c_7286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6254,c_7284])).

tff(c_7288,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_6865])).

tff(c_7292,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_7288,c_6418])).

tff(c_7287,plain,
    ( ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_5'),'#skF_5')
    | k3_xboole_0('#skF_7','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6865])).

tff(c_7352,plain,(
    k3_xboole_0('#skF_7','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7292,c_7287])).

tff(c_6675,plain,(
    ! [A_534,B_535] :
      ( r2_hidden('#skF_2'(A_534,B_535,A_534),A_534)
      | k3_xboole_0(A_534,B_535) = A_534 ) ),
    inference(resolution,[status(thm)],[c_6643,c_14])).

tff(c_6736,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | k3_xboole_0('#skF_7','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6694,c_6707])).

tff(c_7825,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7352,c_6736])).

tff(c_7826,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_6254,c_7825])).

tff(c_7827,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_7826])).

tff(c_7905,plain,(
    k3_xboole_0('#skF_7','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6675,c_7827])).

tff(c_7915,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7352,c_7905])).

tff(c_7917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6254,c_7915])).

tff(c_7919,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_7826])).

tff(c_7943,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_7919,c_6418])).

tff(c_7918,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_5','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_7826])).

tff(c_7921,plain,
    ( ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | k3_xboole_0('#skF_7','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_7918,c_8])).

tff(c_7929,plain,
    ( ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7352,c_7921])).

tff(c_7930,plain,
    ( ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_6254,c_7929])).

tff(c_7960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7919,c_7943,c_7930])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.24/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.24/2.82  
% 8.24/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.24/2.83  %$ r2_hidden > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 8.24/2.83  
% 8.24/2.83  %Foreground sorts:
% 8.24/2.83  
% 8.24/2.83  
% 8.24/2.83  %Background operators:
% 8.24/2.83  
% 8.24/2.83  
% 8.24/2.83  %Foreground operators:
% 8.24/2.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.24/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.24/2.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.24/2.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.24/2.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.24/2.83  tff('#skF_7', type, '#skF_7': $i).
% 8.24/2.83  tff('#skF_5', type, '#skF_5': $i).
% 8.24/2.83  tff('#skF_6', type, '#skF_6': $i).
% 8.24/2.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.24/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.24/2.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.24/2.83  tff('#skF_4', type, '#skF_4': $i).
% 8.24/2.83  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.24/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.24/2.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.24/2.83  
% 8.24/2.85  tff(f_59, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 8.24/2.85  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.24/2.85  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.24/2.85  tff(f_48, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 8.24/2.85  tff(c_28, plain, ('#skF_7'!='#skF_5' | '#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.24/2.85  tff(c_35, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_28])).
% 8.24/2.85  tff(c_384, plain, (![A_67, B_68, C_69]: (r2_hidden('#skF_1'(A_67, B_68, C_69), B_68) | r2_hidden('#skF_2'(A_67, B_68, C_69), C_69) | k3_xboole_0(A_67, B_68)=C_69)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.24/2.85  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.24/2.85  tff(c_34, plain, (k2_zfmisc_1('#skF_6', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.24/2.85  tff(c_94, plain, (![A_39, B_40, C_41, D_42]: (r2_hidden(k4_tarski(A_39, B_40), k2_zfmisc_1(C_41, D_42)) | ~r2_hidden(B_40, D_42) | ~r2_hidden(A_39, C_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.24/2.85  tff(c_138, plain, (![A_45, B_46]: (r2_hidden(k4_tarski(A_45, B_46), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_46, '#skF_7') | ~r2_hidden(A_45, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_94])).
% 8.24/2.85  tff(c_26, plain, (![A_9, C_11, B_10, D_12]: (r2_hidden(A_9, C_11) | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.24/2.85  tff(c_152, plain, (![A_45, B_46]: (r2_hidden(A_45, '#skF_4') | ~r2_hidden(B_46, '#skF_7') | ~r2_hidden(A_45, '#skF_6'))), inference(resolution, [status(thm)], [c_138, c_26])).
% 8.24/2.85  tff(c_180, plain, (![B_49]: (~r2_hidden(B_49, '#skF_7'))), inference(splitLeft, [status(thm)], [c_152])).
% 8.24/2.85  tff(c_195, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_20, c_180])).
% 8.24/2.85  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.24/2.85  tff(c_210, plain, ('#skF_7'!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_195, c_30])).
% 8.24/2.85  tff(c_269, plain, (![A_58]: (r2_hidden('#skF_3'(A_58), A_58) | A_58='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_20])).
% 8.24/2.85  tff(c_177, plain, (![B_46]: (~r2_hidden(B_46, '#skF_7'))), inference(splitLeft, [status(thm)], [c_152])).
% 8.24/2.85  tff(c_32, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.24/2.85  tff(c_53, plain, (![B_20, D_21, A_22, C_23]: (r2_hidden(B_20, D_21) | ~r2_hidden(k4_tarski(A_22, B_20), k2_zfmisc_1(C_23, D_21)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.24/2.85  tff(c_56, plain, (![B_20, A_22]: (r2_hidden(B_20, '#skF_7') | ~r2_hidden(k4_tarski(A_22, B_20), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_53])).
% 8.24/2.85  tff(c_114, plain, (![B_40, A_39]: (r2_hidden(B_40, '#skF_7') | ~r2_hidden(B_40, '#skF_5') | ~r2_hidden(A_39, '#skF_4'))), inference(resolution, [status(thm)], [c_94, c_56])).
% 8.24/2.85  tff(c_156, plain, (![A_47]: (~r2_hidden(A_47, '#skF_4'))), inference(splitLeft, [status(thm)], [c_114])).
% 8.24/2.85  tff(c_168, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_20, c_156])).
% 8.24/2.85  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_168])).
% 8.24/2.85  tff(c_175, plain, (![B_40]: (r2_hidden(B_40, '#skF_7') | ~r2_hidden(B_40, '#skF_5'))), inference(splitRight, [status(thm)], [c_114])).
% 8.24/2.85  tff(c_178, plain, (![B_40]: (~r2_hidden(B_40, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_177, c_175])).
% 8.24/2.85  tff(c_273, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_269, c_178])).
% 8.24/2.85  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_273])).
% 8.24/2.85  tff(c_290, plain, (![A_45]: (r2_hidden(A_45, '#skF_4') | ~r2_hidden(A_45, '#skF_6'))), inference(splitRight, [status(thm)], [c_152])).
% 8.24/2.85  tff(c_1707, plain, (![A_199, C_200]: (r2_hidden('#skF_1'(A_199, '#skF_6', C_200), '#skF_4') | r2_hidden('#skF_2'(A_199, '#skF_6', C_200), C_200) | k3_xboole_0(A_199, '#skF_6')=C_200)), inference(resolution, [status(thm)], [c_384, c_290])).
% 8.24/2.85  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.24/2.85  tff(c_1737, plain, (![A_199]: (r2_hidden('#skF_2'(A_199, '#skF_6', '#skF_4'), '#skF_4') | k3_xboole_0(A_199, '#skF_6')='#skF_4')), inference(resolution, [status(thm)], [c_1707, c_14])).
% 8.24/2.85  tff(c_58, plain, (![A_26, C_27, B_28, D_29]: (r2_hidden(A_26, C_27) | ~r2_hidden(k4_tarski(A_26, B_28), k2_zfmisc_1(C_27, D_29)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.24/2.85  tff(c_61, plain, (![A_26, B_28]: (r2_hidden(A_26, '#skF_6') | ~r2_hidden(k4_tarski(A_26, B_28), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_58])).
% 8.24/2.85  tff(c_112, plain, (![A_39, B_40]: (r2_hidden(A_39, '#skF_6') | ~r2_hidden(B_40, '#skF_5') | ~r2_hidden(A_39, '#skF_4'))), inference(resolution, [status(thm)], [c_94, c_61])).
% 8.24/2.85  tff(c_117, plain, (![B_43]: (~r2_hidden(B_43, '#skF_5'))), inference(splitLeft, [status(thm)], [c_112])).
% 8.24/2.85  tff(c_129, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_20, c_117])).
% 8.24/2.85  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_129])).
% 8.24/2.85  tff(c_136, plain, (![A_39]: (r2_hidden(A_39, '#skF_6') | ~r2_hidden(A_39, '#skF_4'))), inference(splitRight, [status(thm)], [c_112])).
% 8.24/2.85  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.24/2.85  tff(c_291, plain, (![A_59, B_60, C_61]: (~r2_hidden('#skF_1'(A_59, B_60, C_61), C_61) | r2_hidden('#skF_2'(A_59, B_60, C_61), C_61) | k3_xboole_0(A_59, B_60)=C_61)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.24/2.85  tff(c_1222, plain, (![A_154, B_155]: (r2_hidden('#skF_2'(A_154, B_155, '#skF_6'), '#skF_6') | k3_xboole_0(A_154, B_155)='#skF_6' | ~r2_hidden('#skF_1'(A_154, B_155, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_136, c_291])).
% 8.24/2.85  tff(c_1252, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_4', B_2, '#skF_6'), '#skF_6') | k3_xboole_0('#skF_4', B_2)='#skF_6')), inference(resolution, [status(thm)], [c_18, c_1222])).
% 8.24/2.85  tff(c_476, plain, (![A_72, B_73]: (r2_hidden('#skF_2'(A_72, B_73, B_73), B_73) | k3_xboole_0(A_72, B_73)=B_73)), inference(resolution, [status(thm)], [c_384, c_14])).
% 8.24/2.85  tff(c_494, plain, (![A_72]: (r2_hidden('#skF_2'(A_72, '#skF_6', '#skF_6'), '#skF_4') | k3_xboole_0(A_72, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_476, c_290])).
% 8.24/2.85  tff(c_800, plain, (![A_119, B_120, C_121]: (r2_hidden('#skF_1'(A_119, B_120, C_121), B_120) | ~r2_hidden('#skF_2'(A_119, B_120, C_121), B_120) | ~r2_hidden('#skF_2'(A_119, B_120, C_121), A_119) | k3_xboole_0(A_119, B_120)=C_121)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.24/2.85  tff(c_830, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_6', '#skF_6'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_6'), '#skF_6') | k3_xboole_0('#skF_4', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_494, c_800])).
% 8.24/2.85  tff(c_2072, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_830])).
% 8.24/2.85  tff(c_2086, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_1252, c_2072])).
% 8.24/2.85  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.24/2.85  tff(c_1144, plain, (![C_148, B_149]: (~r2_hidden('#skF_2'(C_148, B_149, C_148), B_149) | r2_hidden('#skF_1'(C_148, B_149, C_148), B_149) | k3_xboole_0(C_148, B_149)=C_148)), inference(resolution, [status(thm)], [c_16, c_800])).
% 8.24/2.85  tff(c_1212, plain, (![C_153]: (r2_hidden('#skF_1'(C_153, '#skF_6', C_153), '#skF_4') | ~r2_hidden('#skF_2'(C_153, '#skF_6', C_153), '#skF_6') | k3_xboole_0(C_153, '#skF_6')=C_153)), inference(resolution, [status(thm)], [c_1144, c_290])).
% 8.24/2.85  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.24/2.85  tff(c_1220, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_6') | k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_1212, c_8])).
% 8.24/2.85  tff(c_3879, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_6') | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2086, c_1220])).
% 8.24/2.85  tff(c_3880, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_35, c_3879])).
% 8.24/2.85  tff(c_3881, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_3880])).
% 8.24/2.85  tff(c_3885, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_136, c_3881])).
% 8.24/2.85  tff(c_3896, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_1737, c_3885])).
% 8.24/2.85  tff(c_3898, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3896, c_2086])).
% 8.24/2.85  tff(c_3900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_3898])).
% 8.24/2.85  tff(c_3901, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_3880])).
% 8.24/2.85  tff(c_3913, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_1737, c_3901])).
% 8.24/2.85  tff(c_3998, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3913, c_2086])).
% 8.24/2.85  tff(c_4000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_3998])).
% 8.24/2.85  tff(c_4002, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_830])).
% 8.24/2.85  tff(c_4009, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_4002, c_290])).
% 8.24/2.85  tff(c_4001, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_6' | r2_hidden('#skF_1'('#skF_4', '#skF_6', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_830])).
% 8.24/2.85  tff(c_4043, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_6', '#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_4001])).
% 8.24/2.85  tff(c_4045, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_6'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_6'), '#skF_4') | k3_xboole_0('#skF_4', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_4043, c_8])).
% 8.24/2.85  tff(c_4054, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4009, c_4002, c_4045])).
% 8.24/2.85  tff(c_4368, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_6') | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4054, c_1220])).
% 8.24/2.85  tff(c_4369, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_35, c_4368])).
% 8.24/2.85  tff(c_4370, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_4369])).
% 8.24/2.85  tff(c_4374, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_136, c_4370])).
% 8.24/2.85  tff(c_4385, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_1737, c_4374])).
% 8.24/2.85  tff(c_4387, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4385, c_4054])).
% 8.24/2.85  tff(c_4389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_4387])).
% 8.24/2.85  tff(c_4390, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_4369])).
% 8.24/2.85  tff(c_4488, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_1737, c_4390])).
% 8.24/2.85  tff(c_4490, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4488, c_4054])).
% 8.24/2.85  tff(c_4492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_4490])).
% 8.24/2.85  tff(c_4493, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_4001])).
% 8.65/2.85  tff(c_6174, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_6') | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4493, c_1220])).
% 8.65/2.85  tff(c_6175, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_35, c_6174])).
% 8.65/2.85  tff(c_6176, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_6175])).
% 8.65/2.85  tff(c_6221, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_136, c_6176])).
% 8.65/2.85  tff(c_6232, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_1737, c_6221])).
% 8.65/2.85  tff(c_6234, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6232, c_4493])).
% 8.65/2.85  tff(c_6236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_6234])).
% 8.65/2.85  tff(c_6237, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_6', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_6175])).
% 8.65/2.85  tff(c_6249, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_1737, c_6237])).
% 8.65/2.85  tff(c_6251, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6249, c_4493])).
% 8.65/2.85  tff(c_6253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_6251])).
% 8.65/2.85  tff(c_6254, plain, ('#skF_7'!='#skF_5'), inference(splitRight, [status(thm)], [c_28])).
% 8.65/2.85  tff(c_6643, plain, (![A_534, B_535, C_536]: (r2_hidden('#skF_1'(A_534, B_535, C_536), A_534) | r2_hidden('#skF_2'(A_534, B_535, C_536), C_536) | k3_xboole_0(A_534, B_535)=C_536)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.65/2.85  tff(c_6255, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 8.65/2.85  tff(c_6261, plain, (k2_zfmisc_1('#skF_4', '#skF_7')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6255, c_34])).
% 8.65/2.85  tff(c_6318, plain, (![A_489, B_490, C_491, D_492]: (r2_hidden(k4_tarski(A_489, B_490), k2_zfmisc_1(C_491, D_492)) | ~r2_hidden(B_490, D_492) | ~r2_hidden(A_489, C_491))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.65/2.85  tff(c_6385, plain, (![A_498, B_499]: (r2_hidden(k4_tarski(A_498, B_499), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_499, '#skF_7') | ~r2_hidden(A_498, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6261, c_6318])).
% 8.65/2.85  tff(c_24, plain, (![B_10, D_12, A_9, C_11]: (r2_hidden(B_10, D_12) | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.65/2.85  tff(c_6397, plain, (![B_499, A_498]: (r2_hidden(B_499, '#skF_5') | ~r2_hidden(B_499, '#skF_7') | ~r2_hidden(A_498, '#skF_4'))), inference(resolution, [status(thm)], [c_6385, c_24])).
% 8.65/2.85  tff(c_6399, plain, (![A_500]: (~r2_hidden(A_500, '#skF_4'))), inference(splitLeft, [status(thm)], [c_6397])).
% 8.65/2.85  tff(c_6411, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_20, c_6399])).
% 8.65/2.85  tff(c_6417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_6411])).
% 8.65/2.85  tff(c_6418, plain, (![B_499]: (r2_hidden(B_499, '#skF_5') | ~r2_hidden(B_499, '#skF_7'))), inference(splitRight, [status(thm)], [c_6397])).
% 8.65/2.85  tff(c_6806, plain, (![B_559, C_560]: (r2_hidden('#skF_1'('#skF_7', B_559, C_560), '#skF_5') | r2_hidden('#skF_2'('#skF_7', B_559, C_560), C_560) | k3_xboole_0('#skF_7', B_559)=C_560)), inference(resolution, [status(thm)], [c_6643, c_6418])).
% 8.65/2.85  tff(c_6829, plain, (![B_559]: (r2_hidden('#skF_2'('#skF_7', B_559, '#skF_5'), '#skF_5') | k3_xboole_0('#skF_7', B_559)='#skF_5')), inference(resolution, [status(thm)], [c_6806, c_14])).
% 8.65/2.85  tff(c_6278, plain, (![B_472, D_473, A_474, C_475]: (r2_hidden(B_472, D_473) | ~r2_hidden(k4_tarski(A_474, B_472), k2_zfmisc_1(C_475, D_473)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.65/2.85  tff(c_6281, plain, (![B_472, A_474]: (r2_hidden(B_472, '#skF_7') | ~r2_hidden(k4_tarski(A_474, B_472), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_6261, c_6278])).
% 8.65/2.85  tff(c_6332, plain, (![B_490, A_489]: (r2_hidden(B_490, '#skF_7') | ~r2_hidden(B_490, '#skF_5') | ~r2_hidden(A_489, '#skF_4'))), inference(resolution, [status(thm)], [c_6318, c_6281])).
% 8.65/2.85  tff(c_6357, plain, (![A_496]: (~r2_hidden(A_496, '#skF_4'))), inference(splitLeft, [status(thm)], [c_6332])).
% 8.65/2.85  tff(c_6375, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_20, c_6357])).
% 8.65/2.85  tff(c_6382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_6375])).
% 8.65/2.85  tff(c_6383, plain, (![B_490]: (r2_hidden(B_490, '#skF_7') | ~r2_hidden(B_490, '#skF_5'))), inference(splitRight, [status(thm)], [c_6332])).
% 8.65/2.85  tff(c_6707, plain, (![A_548, B_549, C_550]: (r2_hidden('#skF_1'(A_548, B_549, C_550), A_548) | ~r2_hidden('#skF_2'(A_548, B_549, C_550), B_549) | ~r2_hidden('#skF_2'(A_548, B_549, C_550), A_548) | k3_xboole_0(A_548, B_549)=C_550)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.65/2.85  tff(c_6744, plain, (![A_553, C_554]: (~r2_hidden('#skF_2'(A_553, C_554, C_554), A_553) | r2_hidden('#skF_1'(A_553, C_554, C_554), A_553) | k3_xboole_0(A_553, C_554)=C_554)), inference(resolution, [status(thm)], [c_18, c_6707])).
% 8.65/2.85  tff(c_6767, plain, (![C_554]: (r2_hidden('#skF_1'('#skF_7', C_554, C_554), '#skF_5') | ~r2_hidden('#skF_2'('#skF_7', C_554, C_554), '#skF_7') | k3_xboole_0('#skF_7', C_554)=C_554)), inference(resolution, [status(thm)], [c_6744, c_6418])).
% 8.65/2.85  tff(c_6838, plain, (![A_562, B_563, C_564]: (~r2_hidden('#skF_1'(A_562, B_563, C_564), C_564) | ~r2_hidden('#skF_2'(A_562, B_563, C_564), B_563) | ~r2_hidden('#skF_2'(A_562, B_563, C_564), A_562) | k3_xboole_0(A_562, B_563)=C_564)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.65/2.85  tff(c_6865, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_5'), '#skF_7') | k3_xboole_0('#skF_7', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_6767, c_6838])).
% 8.65/2.85  tff(c_7015, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_6865])).
% 8.65/2.85  tff(c_7019, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_6383, c_7015])).
% 8.65/2.85  tff(c_7029, plain, (k3_xboole_0('#skF_7', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_6829, c_7019])).
% 8.65/2.85  tff(c_6681, plain, (![A_537, B_538]: (r2_hidden('#skF_2'(A_537, B_538, A_537), A_537) | k3_xboole_0(A_537, B_538)=A_537)), inference(resolution, [status(thm)], [c_6643, c_14])).
% 8.65/2.85  tff(c_6694, plain, (![B_538]: (r2_hidden('#skF_2'('#skF_7', B_538, '#skF_7'), '#skF_5') | k3_xboole_0('#skF_7', B_538)='#skF_7')), inference(resolution, [status(thm)], [c_6681, c_6418])).
% 8.65/2.85  tff(c_6531, plain, (![A_517, B_518, C_519]: (r2_hidden('#skF_1'(A_517, B_518, C_519), B_518) | r2_hidden('#skF_2'(A_517, B_518, C_519), C_519) | k3_xboole_0(A_517, B_518)=C_519)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.65/2.85  tff(c_6449, plain, (![A_502, B_503, C_504]: (~r2_hidden('#skF_1'(A_502, B_503, C_504), C_504) | r2_hidden('#skF_2'(A_502, B_503, C_504), C_504) | k3_xboole_0(A_502, B_503)=C_504)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.65/2.85  tff(c_6458, plain, (![A_502, B_503]: (r2_hidden('#skF_2'(A_502, B_503, '#skF_7'), '#skF_7') | k3_xboole_0(A_502, B_503)='#skF_7' | ~r2_hidden('#skF_1'(A_502, B_503, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_6383, c_6449])).
% 8.65/2.85  tff(c_6562, plain, (![A_517]: (r2_hidden('#skF_2'(A_517, '#skF_5', '#skF_7'), '#skF_7') | k3_xboole_0(A_517, '#skF_5')='#skF_7')), inference(resolution, [status(thm)], [c_6531, c_6458])).
% 8.65/2.85  tff(c_7084, plain, (![A_567, B_568, C_569]: (r2_hidden('#skF_1'(A_567, B_568, C_569), B_568) | ~r2_hidden('#skF_2'(A_567, B_568, C_569), B_568) | ~r2_hidden('#skF_2'(A_567, B_568, C_569), A_567) | k3_xboole_0(A_567, B_568)=C_569)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.65/2.85  tff(c_7102, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_5', '#skF_7'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_5') | k3_xboole_0('#skF_7', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_6562, c_7084])).
% 8.65/2.85  tff(c_7126, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_5', '#skF_7'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_5') | '#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7029, c_7102])).
% 8.65/2.85  tff(c_7127, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_5', '#skF_7'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_6254, c_7126])).
% 8.65/2.85  tff(c_7237, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_7127])).
% 8.65/2.85  tff(c_7240, plain, (k3_xboole_0('#skF_7', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_6694, c_7237])).
% 8.65/2.85  tff(c_7245, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7029, c_7240])).
% 8.65/2.85  tff(c_7247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6254, c_7245])).
% 8.65/2.85  tff(c_7248, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_5', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_7127])).
% 8.65/2.85  tff(c_7252, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | k3_xboole_0('#skF_7', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_7248, c_6458])).
% 8.65/2.85  tff(c_7254, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | '#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7029, c_7252])).
% 8.65/2.85  tff(c_7255, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_6254, c_7254])).
% 8.65/2.85  tff(c_7249, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_7127])).
% 8.65/2.85  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.65/2.85  tff(c_7257, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | k3_xboole_0('#skF_7', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_7249, c_12])).
% 8.65/2.85  tff(c_7259, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | '#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7029, c_7257])).
% 8.65/2.85  tff(c_7260, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_6254, c_7259])).
% 8.65/2.85  tff(c_7273, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_5', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7255, c_7260])).
% 8.65/2.85  tff(c_7275, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | k3_xboole_0('#skF_7', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_7273, c_8])).
% 8.65/2.85  tff(c_7284, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7029, c_7255, c_7249, c_7275])).
% 8.65/2.85  tff(c_7286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6254, c_7284])).
% 8.65/2.85  tff(c_7288, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_5'), '#skF_7')), inference(splitRight, [status(thm)], [c_6865])).
% 8.65/2.85  tff(c_7292, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_7288, c_6418])).
% 8.65/2.85  tff(c_7287, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_5'), '#skF_5') | k3_xboole_0('#skF_7', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_6865])).
% 8.65/2.85  tff(c_7352, plain, (k3_xboole_0('#skF_7', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7292, c_7287])).
% 8.65/2.85  tff(c_6675, plain, (![A_534, B_535]: (r2_hidden('#skF_2'(A_534, B_535, A_534), A_534) | k3_xboole_0(A_534, B_535)=A_534)), inference(resolution, [status(thm)], [c_6643, c_14])).
% 8.65/2.85  tff(c_6736, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | k3_xboole_0('#skF_7', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_6694, c_6707])).
% 8.65/2.85  tff(c_7825, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | '#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7352, c_6736])).
% 8.65/2.85  tff(c_7826, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_6254, c_7825])).
% 8.65/2.85  tff(c_7827, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_7826])).
% 8.65/2.85  tff(c_7905, plain, (k3_xboole_0('#skF_7', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_6675, c_7827])).
% 8.65/2.85  tff(c_7915, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7352, c_7905])).
% 8.65/2.85  tff(c_7917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6254, c_7915])).
% 8.65/2.85  tff(c_7919, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_7826])).
% 8.65/2.85  tff(c_7943, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_7919, c_6418])).
% 8.65/2.85  tff(c_7918, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_5', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_7826])).
% 8.65/2.85  tff(c_7921, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | k3_xboole_0('#skF_7', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_7918, c_8])).
% 8.65/2.85  tff(c_7929, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7') | '#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7352, c_7921])).
% 8.65/2.85  tff(c_7930, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_5') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_6254, c_7929])).
% 8.65/2.85  tff(c_7960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7919, c_7943, c_7930])).
% 8.65/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.65/2.85  
% 8.65/2.85  Inference rules
% 8.65/2.85  ----------------------
% 8.65/2.85  #Ref     : 0
% 8.65/2.85  #Sup     : 1640
% 8.65/2.85  #Fact    : 0
% 8.65/2.85  #Define  : 0
% 8.65/2.85  #Split   : 28
% 8.65/2.85  #Chain   : 0
% 8.65/2.85  #Close   : 0
% 8.65/2.85  
% 8.65/2.85  Ordering : KBO
% 8.65/2.85  
% 8.65/2.85  Simplification rules
% 8.65/2.85  ----------------------
% 8.65/2.85  #Subsume      : 663
% 8.65/2.85  #Demod        : 1084
% 8.65/2.85  #Tautology    : 221
% 8.65/2.85  #SimpNegUnit  : 116
% 8.65/2.85  #BackRed      : 30
% 8.65/2.85  
% 8.65/2.85  #Partial instantiations: 0
% 8.65/2.85  #Strategies tried      : 1
% 8.65/2.85  
% 8.65/2.85  Timing (in seconds)
% 8.65/2.85  ----------------------
% 8.65/2.86  Preprocessing        : 0.29
% 8.65/2.86  Parsing              : 0.16
% 8.65/2.86  CNF conversion       : 0.02
% 8.65/2.86  Main loop            : 1.73
% 8.65/2.86  Inferencing          : 0.66
% 8.65/2.86  Reduction            : 0.46
% 8.65/2.86  Demodulation         : 0.29
% 8.65/2.86  BG Simplification    : 0.05
% 8.65/2.86  Subsumption          : 0.45
% 8.65/2.86  Abstraction          : 0.07
% 8.65/2.86  MUC search           : 0.00
% 8.65/2.86  Cooper               : 0.00
% 8.65/2.86  Total                : 2.08
% 8.65/2.86  Index Insertion      : 0.00
% 8.65/2.86  Index Deletion       : 0.00
% 8.65/2.86  Index Matching       : 0.00
% 8.65/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
