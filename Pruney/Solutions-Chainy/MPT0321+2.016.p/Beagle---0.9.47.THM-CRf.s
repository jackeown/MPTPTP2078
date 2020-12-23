%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:15 EST 2020

% Result     : Theorem 36.24s
% Output     : CNFRefutation 36.57s
% Verified   : 
% Statistics : Number of formulae       :  299 (3483 expanded)
%              Number of leaves         :   36 (1183 expanded)
%              Depth                    :   32
%              Number of atoms          :  447 (6462 expanded)
%              Number of equality atoms :  215 (3055 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_78,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_82,plain,
    ( '#skF_10' != '#skF_12'
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_99,plain,(
    '#skF_11' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [C_34] : r2_hidden(C_34,k1_tarski(C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,(
    ! [A_29] : k4_xboole_0(k1_xboole_0,A_29) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_214,plain,(
    ! [D_66,B_67,A_68] :
      ( ~ r2_hidden(D_66,B_67)
      | ~ r2_hidden(D_66,k4_xboole_0(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_218,plain,(
    ! [D_69,A_70] :
      ( ~ r2_hidden(D_69,A_70)
      | ~ r2_hidden(D_69,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_214])).

tff(c_221,plain,(
    ! [C_34] : ~ r2_hidden(C_34,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64,c_218])).

tff(c_278,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_1'(A_81,B_82),A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    ! [D_19,A_14,B_15] :
      ( r2_hidden(D_19,A_14)
      | ~ r2_hidden(D_19,k4_xboole_0(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10861,plain,(
    ! [A_3394,B_3395,B_3396] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_3394,B_3395),B_3396),A_3394)
      | r1_tarski(k4_xboole_0(A_3394,B_3395),B_3396) ) ),
    inference(resolution,[status(thm)],[c_278,c_32])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10910,plain,(
    ! [A_3397,B_3398] : r1_tarski(k4_xboole_0(A_3397,B_3398),A_3397) ),
    inference(resolution,[status(thm)],[c_10861,c_6])).

tff(c_58,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10966,plain,(
    ! [A_3399,B_3400] : k3_xboole_0(k4_xboole_0(A_3399,B_3400),A_3399) = k4_xboole_0(A_3399,B_3400) ),
    inference(resolution,[status(thm)],[c_10910,c_58])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_11064,plain,(
    ! [A_3399,B_3400] : k3_xboole_0(A_3399,k4_xboole_0(A_3399,B_3400)) = k4_xboole_0(A_3399,B_3400) ),
    inference(superposition,[status(thm),theory(equality)],[c_10966,c_2])).

tff(c_78,plain,(
    ! [B_36] : k2_zfmisc_1(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_320,plain,(
    ! [B_84] : r1_tarski(k1_xboole_0,B_84) ),
    inference(resolution,[status(thm)],[c_278,c_221])).

tff(c_324,plain,(
    ! [B_84] : k3_xboole_0(k1_xboole_0,B_84) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_320,c_58])).

tff(c_325,plain,(
    ! [B_85] : k3_xboole_0(k1_xboole_0,B_85) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_320,c_58])).

tff(c_336,plain,(
    ! [B_85] : k3_xboole_0(B_85,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_2])).

tff(c_8031,plain,(
    ! [A_3292,B_3293,C_3294] :
      ( r2_hidden('#skF_2'(A_3292,B_3293,C_3294),A_3292)
      | r2_hidden('#skF_3'(A_3292,B_3293,C_3294),C_3294)
      | k3_xboole_0(A_3292,B_3293) = C_3294 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_37187,plain,(
    ! [A_3832,B_3833,A_3834,B_3835] :
      ( r2_hidden('#skF_3'(A_3832,B_3833,k3_xboole_0(A_3834,B_3835)),B_3835)
      | r2_hidden('#skF_2'(A_3832,B_3833,k3_xboole_0(A_3834,B_3835)),A_3832)
      | k3_xboole_0(A_3834,B_3835) = k3_xboole_0(A_3832,B_3833) ) ),
    inference(resolution,[status(thm)],[c_8031,c_12])).

tff(c_37460,plain,(
    ! [A_3832,B_3833,B_85] :
      ( r2_hidden('#skF_3'(A_3832,B_3833,k3_xboole_0(B_85,k1_xboole_0)),k1_xboole_0)
      | r2_hidden('#skF_2'(A_3832,B_3833,k1_xboole_0),A_3832)
      | k3_xboole_0(B_85,k1_xboole_0) = k3_xboole_0(A_3832,B_3833) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_37187])).

tff(c_37554,plain,(
    ! [A_3832,B_3833] :
      ( r2_hidden('#skF_3'(A_3832,B_3833,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_2'(A_3832,B_3833,k1_xboole_0),A_3832)
      | k3_xboole_0(A_3832,B_3833) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_336,c_37460])).

tff(c_37555,plain,(
    ! [A_3832,B_3833] :
      ( r2_hidden('#skF_2'(A_3832,B_3833,k1_xboole_0),A_3832)
      | k3_xboole_0(A_3832,B_3833) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_37554])).

tff(c_7576,plain,(
    ! [A_3266,B_3267,C_3268] :
      ( r2_hidden('#skF_2'(A_3266,B_3267,C_3268),B_3267)
      | r2_hidden('#skF_3'(A_3266,B_3267,C_3268),C_3268)
      | k3_xboole_0(A_3266,B_3267) = C_3268 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [D_19,B_15,A_14] :
      ( ~ r2_hidden(D_19,B_15)
      | ~ r2_hidden(D_19,k4_xboole_0(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42903,plain,(
    ! [A_3892,A_3893,B_3894,C_3895] :
      ( ~ r2_hidden('#skF_2'(A_3892,k4_xboole_0(A_3893,B_3894),C_3895),B_3894)
      | r2_hidden('#skF_3'(A_3892,k4_xboole_0(A_3893,B_3894),C_3895),C_3895)
      | k3_xboole_0(A_3892,k4_xboole_0(A_3893,B_3894)) = C_3895 ) ),
    inference(resolution,[status(thm)],[c_7576,c_30])).

tff(c_42912,plain,(
    ! [A_3832,A_3893] :
      ( r2_hidden('#skF_3'(A_3832,k4_xboole_0(A_3893,A_3832),k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(A_3832,k4_xboole_0(A_3893,A_3832)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_37555,c_42903])).

tff(c_42976,plain,(
    ! [A_3896,A_3897] : k3_xboole_0(A_3896,k4_xboole_0(A_3897,A_3896)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_42912])).

tff(c_9785,plain,(
    ! [A_3374,B_3375,B_3376] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_3374,B_3375),B_3376),B_3375)
      | r1_tarski(k3_xboole_0(A_3374,B_3375),B_3376) ) ),
    inference(resolution,[status(thm)],[c_278,c_12])).

tff(c_9857,plain,(
    ! [A_3377,B_3378] : r1_tarski(k3_xboole_0(A_3377,B_3378),B_3378) ),
    inference(resolution,[status(thm)],[c_9785,c_6])).

tff(c_9937,plain,(
    ! [B_3379,A_3380] : r1_tarski(k3_xboole_0(B_3379,A_3380),B_3379) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9857])).

tff(c_10231,plain,(
    ! [B_3386,A_3387] : k3_xboole_0(k3_xboole_0(B_3386,A_3387),B_3386) = k3_xboole_0(B_3386,A_3387) ),
    inference(resolution,[status(thm)],[c_9937,c_58])).

tff(c_11786,plain,(
    ! [B_3412,A_3413] : k3_xboole_0(k3_xboole_0(B_3412,A_3413),A_3413) = k3_xboole_0(A_3413,B_3412) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10231])).

tff(c_11981,plain,(
    ! [B_2,B_3412] : k3_xboole_0(B_2,k3_xboole_0(B_3412,B_2)) = k3_xboole_0(B_2,B_3412) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11786])).

tff(c_43388,plain,(
    ! [A_3897,A_3896] : k3_xboole_0(k4_xboole_0(A_3897,A_3896),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_3897,A_3896),A_3896) ),
    inference(superposition,[status(thm),theory(equality)],[c_42976,c_11981])).

tff(c_43685,plain,(
    ! [A_3898,A_3899] : k3_xboole_0(k4_xboole_0(A_3898,A_3899),A_3899) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_2,c_43388])).

tff(c_52,plain,(
    ! [A_22] : k3_xboole_0(A_22,A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_80,plain,(
    ! [A_37,C_39,B_38,D_40] : k3_xboole_0(k2_zfmisc_1(A_37,C_39),k2_zfmisc_1(B_38,D_40)) = k2_zfmisc_1(k3_xboole_0(A_37,B_38),k3_xboole_0(C_39,D_40)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_88,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6912,plain,(
    ! [A_3204,C_3205,B_3206,D_3207] : k3_xboole_0(k2_zfmisc_1(A_3204,C_3205),k2_zfmisc_1(B_3206,D_3207)) = k2_zfmisc_1(k3_xboole_0(A_3204,B_3206),k3_xboole_0(C_3205,D_3207)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7471,plain,(
    ! [A_3204,C_3205] : k3_xboole_0(k2_zfmisc_1(A_3204,C_3205),k2_zfmisc_1('#skF_9','#skF_10')) = k2_zfmisc_1(k3_xboole_0(A_3204,'#skF_11'),k3_xboole_0(C_3205,'#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_6912])).

tff(c_7683,plain,(
    ! [A_3271,C_3272] : k2_zfmisc_1(k3_xboole_0(A_3271,'#skF_11'),k3_xboole_0(C_3272,'#skF_12')) = k2_zfmisc_1(k3_xboole_0(A_3271,'#skF_9'),k3_xboole_0(C_3272,'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_7471])).

tff(c_7730,plain,(
    ! [A_3271] : k2_zfmisc_1(k3_xboole_0(A_3271,'#skF_9'),k3_xboole_0('#skF_12','#skF_10')) = k2_zfmisc_1(k3_xboole_0(A_3271,'#skF_11'),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_7683])).

tff(c_44182,plain,(
    ! [A_3898] : k2_zfmisc_1(k3_xboole_0(k4_xboole_0(A_3898,'#skF_9'),'#skF_11'),'#skF_12') = k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_12','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_43685,c_7730])).

tff(c_47643,plain,(
    ! [A_3921] : k2_zfmisc_1(k3_xboole_0('#skF_11',k4_xboole_0(A_3921,'#skF_9')),'#skF_12') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_78,c_44182])).

tff(c_47839,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_11','#skF_9'),'#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11064,c_47643])).

tff(c_74,plain,(
    ! [B_36,A_35] :
      ( k1_xboole_0 = B_36
      | k1_xboole_0 = A_35
      | k2_zfmisc_1(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48265,plain,
    ( k1_xboole_0 = '#skF_12'
    | k4_xboole_0('#skF_11','#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_47839,c_74])).

tff(c_48267,plain,(
    k4_xboole_0('#skF_11','#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48265])).

tff(c_28,plain,(
    ! [D_19,A_14,B_15] :
      ( r2_hidden(D_19,k4_xboole_0(A_14,B_15))
      | r2_hidden(D_19,B_15)
      | ~ r2_hidden(D_19,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48429,plain,(
    ! [D_19] :
      ( r2_hidden(D_19,k1_xboole_0)
      | r2_hidden(D_19,'#skF_9')
      | ~ r2_hidden(D_19,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48267,c_28])).

tff(c_48499,plain,(
    ! [D_3926] :
      ( r2_hidden(D_3926,'#skF_9')
      | ~ r2_hidden(D_3926,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_48429])).

tff(c_58339,plain,(
    ! [B_4009] :
      ( r2_hidden('#skF_1'('#skF_11',B_4009),'#skF_9')
      | r1_tarski('#skF_11',B_4009) ) ),
    inference(resolution,[status(thm)],[c_8,c_48499])).

tff(c_58355,plain,(
    r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_58339,c_6])).

tff(c_46,plain,(
    ! [A_20,B_21] :
      ( r2_xboole_0(A_20,B_21)
      | B_21 = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_56,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_6'(A_24,B_25),B_25)
      | ~ r2_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_414,plain,(
    ! [C_87,B_88,A_89] :
      ( r2_hidden(C_87,B_88)
      | ~ r2_hidden(C_87,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_587,plain,(
    ! [A_110,B_111,B_112] :
      ( r2_hidden('#skF_6'(A_110,B_111),B_112)
      | ~ r1_tarski(B_111,B_112)
      | ~ r2_xboole_0(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_56,c_414])).

tff(c_54,plain,(
    ! [A_24,B_25] :
      ( ~ r2_hidden('#skF_6'(A_24,B_25),A_24)
      | ~ r2_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_626,plain,(
    ! [B_113,B_114] :
      ( ~ r1_tarski(B_113,B_114)
      | ~ r2_xboole_0(B_114,B_113) ) ),
    inference(resolution,[status(thm)],[c_587,c_54])).

tff(c_630,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | B_21 = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_46,c_626])).

tff(c_58357,plain,
    ( '#skF_11' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_58355,c_630])).

tff(c_58363,plain,(
    ~ r1_tarski('#skF_9','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_58357])).

tff(c_47872,plain,(
    ! [A_3921] :
      ( k1_xboole_0 = '#skF_12'
      | k3_xboole_0('#skF_11',k4_xboole_0(A_3921,'#skF_9')) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47643,c_74])).

tff(c_49834,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_47872])).

tff(c_49896,plain,(
    ! [C_34] : ~ r2_hidden(C_34,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49834,c_221])).

tff(c_76,plain,(
    ! [A_35] : k2_zfmisc_1(A_35,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_49900,plain,(
    ! [A_35] : k2_zfmisc_1(A_35,'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49834,c_49834,c_76])).

tff(c_175,plain,(
    ! [B_55,A_56] :
      ( k1_xboole_0 = B_55
      | k1_xboole_0 = A_56
      | k2_zfmisc_1(A_56,B_55) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_181,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_175])).

tff(c_213,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_8407,plain,(
    ! [A_3314,B_3315,C_3316] :
      ( r2_hidden('#skF_4'(A_3314,B_3315,C_3316),A_3314)
      | r2_hidden('#skF_5'(A_3314,B_3315,C_3316),C_3316)
      | k4_xboole_0(A_3314,B_3315) = C_3316 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    ! [A_14,B_15,C_16] :
      ( ~ r2_hidden('#skF_4'(A_14,B_15,C_16),B_15)
      | r2_hidden('#skF_5'(A_14,B_15,C_16),C_16)
      | k4_xboole_0(A_14,B_15) = C_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8535,plain,(
    ! [A_3321,C_3322] :
      ( r2_hidden('#skF_5'(A_3321,A_3321,C_3322),C_3322)
      | k4_xboole_0(A_3321,A_3321) = C_3322 ) ),
    inference(resolution,[status(thm)],[c_8407,c_42])).

tff(c_8567,plain,(
    ! [A_3321] : k4_xboole_0(A_3321,A_3321) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8535,c_221])).

tff(c_8465,plain,(
    ! [A_3314,C_3316] :
      ( r2_hidden('#skF_5'(A_3314,A_3314,C_3316),C_3316)
      | k4_xboole_0(A_3314,A_3314) = C_3316 ) ),
    inference(resolution,[status(thm)],[c_8407,c_42])).

tff(c_8626,plain,(
    ! [A_3314,C_3316] :
      ( r2_hidden('#skF_5'(A_3314,A_3314,C_3316),C_3316)
      | k1_xboole_0 = C_3316 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8567,c_8465])).

tff(c_14824,plain,(
    ! [B_3477,D_3478,A_3479,C_3480] : k3_xboole_0(k2_zfmisc_1(B_3477,D_3478),k2_zfmisc_1(A_3479,C_3480)) = k2_zfmisc_1(k3_xboole_0(A_3479,B_3477),k3_xboole_0(C_3480,D_3478)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6912,c_2])).

tff(c_9844,plain,(
    ! [A_3374,B_3375] : r1_tarski(k3_xboole_0(A_3374,B_3375),B_3375) ),
    inference(resolution,[status(thm)],[c_9785,c_6])).

tff(c_17710,plain,(
    ! [A_3532,B_3533,C_3534,D_3535] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_3532,B_3533),k3_xboole_0(C_3534,D_3535)),k2_zfmisc_1(A_3532,C_3534)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14824,c_9844])).

tff(c_18107,plain,(
    ! [A_3541,C_3542,D_3543] : r1_tarski(k2_zfmisc_1(A_3541,k3_xboole_0(C_3542,D_3543)),k2_zfmisc_1(A_3541,C_3542)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_17710])).

tff(c_18256,plain,(
    ! [A_3541,A_1,B_2] : r1_tarski(k2_zfmisc_1(A_3541,k3_xboole_0(A_1,B_2)),k2_zfmisc_1(A_3541,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_18107])).

tff(c_7468,plain,(
    ! [B_3206,D_3207] : k3_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1(B_3206,D_3207)) = k2_zfmisc_1(k3_xboole_0('#skF_11',B_3206),k3_xboole_0('#skF_12',D_3207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_6912])).

tff(c_7809,plain,(
    ! [B_3280,D_3281] : k2_zfmisc_1(k3_xboole_0('#skF_11',B_3280),k3_xboole_0('#skF_12',D_3281)) = k2_zfmisc_1(k3_xboole_0('#skF_9',B_3280),k3_xboole_0('#skF_10',D_3281)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_7468])).

tff(c_8337,plain,(
    ! [D_3313] : k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),k3_xboole_0('#skF_10',D_3313)) = k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',D_3313)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_7809])).

tff(c_8380,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),'#skF_10') = k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_8337])).

tff(c_7844,plain,(
    ! [B_2,D_3281] : k2_zfmisc_1(k3_xboole_0(B_2,'#skF_11'),k3_xboole_0('#skF_12',D_3281)) = k2_zfmisc_1(k3_xboole_0('#skF_9',B_2),k3_xboole_0('#skF_10',D_3281)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7809])).

tff(c_19647,plain,(
    ! [A_3576,B_3577,C_3578,D_3579] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_3576,B_3577),k3_xboole_0(C_3578,D_3579)),k2_zfmisc_1(B_3577,D_3579)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_9857])).

tff(c_20270,plain,(
    ! [B_3589,D_3590] : r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_9',B_3589),k3_xboole_0('#skF_10',D_3590)),k2_zfmisc_1('#skF_11',D_3590)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7844,c_19647])).

tff(c_20386,plain,(
    ! [D_3591] : r1_tarski(k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_10',D_3591)),k2_zfmisc_1('#skF_11',D_3591)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_20270])).

tff(c_20438,plain,(
    r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_20386])).

tff(c_20450,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_10')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_20438,c_58])).

tff(c_6930,plain,(
    ! [B_3206,D_3207,A_3204,C_3205] : k3_xboole_0(k2_zfmisc_1(B_3206,D_3207),k2_zfmisc_1(A_3204,C_3205)) = k2_zfmisc_1(k3_xboole_0(A_3204,B_3206),k3_xboole_0(C_3205,D_3207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6912,c_2])).

tff(c_20922,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_11','#skF_9'),k3_xboole_0('#skF_10','#skF_10')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_20450,c_6930])).

tff(c_21043,plain,(
    k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12','#skF_10')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8380,c_2,c_52,c_20922])).

tff(c_21082,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),'#skF_10') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21043,c_8380])).

tff(c_10011,plain,(
    ! [B_3379,A_3380] : k3_xboole_0(k3_xboole_0(B_3379,A_3380),B_3379) = k3_xboole_0(B_3379,A_3380) ),
    inference(resolution,[status(thm)],[c_9937,c_58])).

tff(c_10234,plain,(
    ! [B_3386,A_3387] : k3_xboole_0(k3_xboole_0(B_3386,A_3387),k3_xboole_0(B_3386,A_3387)) = k3_xboole_0(k3_xboole_0(B_3386,A_3387),B_3386) ),
    inference(superposition,[status(thm),theory(equality)],[c_10231,c_10011])).

tff(c_10381,plain,(
    ! [B_3386,A_3387] : k3_xboole_0(B_3386,k3_xboole_0(B_3386,A_3387)) = k3_xboole_0(B_3386,A_3387) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52,c_10234])).

tff(c_8574,plain,(
    ! [A_3323] : k2_zfmisc_1(k3_xboole_0(A_3323,'#skF_9'),k3_xboole_0('#skF_12','#skF_10')) = k2_zfmisc_1(k3_xboole_0(A_3323,'#skF_11'),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_7683])).

tff(c_8617,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),'#skF_12') = k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_12','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_8574])).

tff(c_7714,plain,(
    ! [A_3271,A_1] : k2_zfmisc_1(k3_xboole_0(A_3271,'#skF_11'),k3_xboole_0('#skF_12',A_1)) = k2_zfmisc_1(k3_xboole_0(A_3271,'#skF_9'),k3_xboole_0(A_1,'#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7683])).

tff(c_223,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_6'(A_72,B_73),B_73)
      | ~ r2_xboole_0(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12786,plain,(
    ! [A_3435,A_3436,B_3437] :
      ( r2_hidden('#skF_6'(A_3435,k3_xboole_0(A_3436,B_3437)),B_3437)
      | ~ r2_xboole_0(A_3435,k3_xboole_0(A_3436,B_3437)) ) ),
    inference(resolution,[status(thm)],[c_223,c_12])).

tff(c_12875,plain,(
    ! [B_3437,A_3436] : ~ r2_xboole_0(B_3437,k3_xboole_0(A_3436,B_3437)) ),
    inference(resolution,[status(thm)],[c_12786,c_54])).

tff(c_17466,plain,(
    ! [A_3528,C_3529,B_3530,D_3531] : ~ r2_xboole_0(k2_zfmisc_1(A_3528,C_3529),k2_zfmisc_1(k3_xboole_0(A_3528,B_3530),k3_xboole_0(C_3529,D_3531))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14824,c_12875])).

tff(c_22642,plain,(
    ! [A_3615,A_3616] : ~ r2_xboole_0(k2_zfmisc_1(A_3615,'#skF_12'),k2_zfmisc_1(k3_xboole_0(A_3615,'#skF_9'),k3_xboole_0(A_3616,'#skF_10'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7714,c_17466])).

tff(c_22825,plain,(
    ! [A_3618] : ~ r2_xboole_0(k2_zfmisc_1(A_3618,'#skF_12'),k2_zfmisc_1(k3_xboole_0(A_3618,'#skF_9'),'#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_22642])).

tff(c_22861,plain,(
    ~ r2_xboole_0(k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_12','#skF_10')),k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_9','#skF_11'),'#skF_9'),'#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8617,c_22825])).

tff(c_22895,plain,(
    ~ r2_xboole_0(k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_12','#skF_10')),k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21082,c_10381,c_2,c_22861])).

tff(c_23229,plain,
    ( k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_12','#skF_10')) = k2_zfmisc_1('#skF_9','#skF_10')
    | ~ r1_tarski(k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_12','#skF_10')),k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_46,c_22895])).

tff(c_23232,plain,(
    k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_12','#skF_10')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18256,c_23229])).

tff(c_17937,plain,(
    ! [A_22,C_3534,D_3535] : r1_tarski(k2_zfmisc_1(A_22,k3_xboole_0(C_3534,D_3535)),k2_zfmisc_1(A_22,C_3534)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_17710])).

tff(c_23264,plain,(
    r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_9','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23232,c_17937])).

tff(c_23391,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_9','#skF_12')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_23264,c_58])).

tff(c_23806,plain,(
    ! [D_3633] :
      ( r2_hidden(D_3633,k2_zfmisc_1('#skF_9','#skF_12'))
      | ~ r2_hidden(D_3633,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23391,c_12])).

tff(c_23902,plain,(
    ! [A_3314] :
      ( r2_hidden('#skF_5'(A_3314,A_3314,k2_zfmisc_1('#skF_9','#skF_10')),k2_zfmisc_1('#skF_9','#skF_12'))
      | k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8626,c_23806])).

tff(c_24004,plain,(
    ! [A_3314] : r2_hidden('#skF_5'(A_3314,A_3314,k2_zfmisc_1('#skF_9','#skF_10')),k2_zfmisc_1('#skF_9','#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_23902])).

tff(c_52622,plain,(
    ! [A_3314] : r2_hidden('#skF_5'(A_3314,A_3314,k2_zfmisc_1('#skF_9','#skF_10')),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49900,c_24004])).

tff(c_52654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49896,c_52622])).

tff(c_52656,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_47872])).

tff(c_42961,plain,(
    ! [A_3832,A_3893] : k3_xboole_0(A_3832,k4_xboole_0(A_3893,A_3832)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_42912])).

tff(c_7860,plain,(
    ! [D_3281] : k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),k3_xboole_0('#skF_10',D_3281)) = k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',D_3281)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_7809])).

tff(c_43455,plain,(
    ! [A_3897] : k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',k4_xboole_0(A_3897,'#skF_10'))) = k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42976,c_7860])).

tff(c_44439,plain,(
    ! [A_3900] : k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',k4_xboole_0(A_3900,'#skF_10'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_43455])).

tff(c_44636,plain,(
    k2_zfmisc_1('#skF_11',k4_xboole_0('#skF_12','#skF_10')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11064,c_44439])).

tff(c_44859,plain,
    ( k4_xboole_0('#skF_12','#skF_10') = k1_xboole_0
    | k1_xboole_0 = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_44636,c_74])).

tff(c_44861,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_44859])).

tff(c_44967,plain,(
    ! [B_36] : k2_zfmisc_1('#skF_11',B_36) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44861,c_44861,c_78])).

tff(c_45370,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44967,c_88])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7509,plain,(
    ! [B_3206,D_3207] : k2_zfmisc_1(k3_xboole_0('#skF_11',B_3206),k3_xboole_0('#skF_12',D_3207)) = k2_zfmisc_1(k3_xboole_0('#skF_9',B_3206),k3_xboole_0('#skF_10',D_3207)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_7468])).

tff(c_9225,plain,(
    ! [B_3359,C_3360] : k2_zfmisc_1(k3_xboole_0(B_3359,'#skF_9'),k3_xboole_0(C_3360,'#skF_10')) = k2_zfmisc_1(k3_xboole_0('#skF_11',B_3359),k3_xboole_0(C_3360,'#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7683])).

tff(c_9352,plain,(
    ! [B_3359] : k2_zfmisc_1(k3_xboole_0('#skF_11',B_3359),k3_xboole_0('#skF_10','#skF_12')) = k2_zfmisc_1(k3_xboole_0(B_3359,'#skF_9'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_9225])).

tff(c_9450,plain,(
    ! [B_3362] : k2_zfmisc_1(k3_xboole_0(B_3362,'#skF_9'),'#skF_10') = k2_zfmisc_1(k3_xboole_0('#skF_9',B_3362),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7509,c_2,c_9352])).

tff(c_9471,plain,(
    ! [B_3362] :
      ( k1_xboole_0 = '#skF_10'
      | k3_xboole_0('#skF_9',B_3362) = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0(B_3362,'#skF_9'),'#skF_10') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9450,c_74])).

tff(c_9507,plain,(
    ! [B_3362] :
      ( k3_xboole_0('#skF_9',B_3362) = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0(B_3362,'#skF_9'),'#skF_10') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_9471])).

tff(c_45018,plain,(
    ! [B_3906] :
      ( k3_xboole_0('#skF_9',B_3906) = '#skF_11'
      | k2_zfmisc_1(k3_xboole_0(B_3906,'#skF_9'),'#skF_10') != '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44861,c_44861,c_9507])).

tff(c_45062,plain,
    ( k3_xboole_0('#skF_9','#skF_9') = '#skF_11'
    | k2_zfmisc_1('#skF_9','#skF_10') != '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_45018])).

tff(c_45068,plain,
    ( '#skF_11' = '#skF_9'
    | k2_zfmisc_1('#skF_9','#skF_10') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_45062])).

tff(c_45069,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_45068])).

tff(c_46971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45370,c_45069])).

tff(c_46972,plain,(
    k4_xboole_0('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44859])).

tff(c_47121,plain,(
    ! [D_19] :
      ( r2_hidden(D_19,k1_xboole_0)
      | r2_hidden(D_19,'#skF_10')
      | ~ r2_hidden(D_19,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46972,c_28])).

tff(c_47188,plain,(
    ! [D_3917] :
      ( r2_hidden(D_3917,'#skF_10')
      | ~ r2_hidden(D_3917,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_47121])).

tff(c_55232,plain,(
    ! [A_3976] :
      ( r1_tarski(A_3976,'#skF_10')
      | ~ r2_hidden('#skF_1'(A_3976,'#skF_10'),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_47188,c_6])).

tff(c_55261,plain,(
    r1_tarski('#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_8,c_55232])).

tff(c_55268,plain,(
    k3_xboole_0('#skF_12','#skF_10') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_55261,c_58])).

tff(c_7864,plain,(
    ! [B_3280] : k2_zfmisc_1(k3_xboole_0('#skF_9',B_3280),k3_xboole_0('#skF_10','#skF_12')) = k2_zfmisc_1(k3_xboole_0('#skF_11',B_3280),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_7809])).

tff(c_7873,plain,(
    ! [B_3280] : k2_zfmisc_1(k3_xboole_0('#skF_9',B_3280),k3_xboole_0('#skF_12','#skF_10')) = k2_zfmisc_1(k3_xboole_0('#skF_11',B_3280),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7864])).

tff(c_82035,plain,(
    ! [B_4316] : k2_zfmisc_1(k3_xboole_0('#skF_11',B_4316),'#skF_12') = k2_zfmisc_1(k3_xboole_0('#skF_9',B_4316),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55268,c_7873])).

tff(c_82269,plain,(
    ! [A_3893] : k2_zfmisc_1(k3_xboole_0('#skF_9',k4_xboole_0(A_3893,'#skF_11')),'#skF_12') = k2_zfmisc_1(k1_xboole_0,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_42961,c_82035])).

tff(c_82366,plain,(
    ! [A_4317] : k2_zfmisc_1(k3_xboole_0('#skF_9',k4_xboole_0(A_4317,'#skF_11')),'#skF_12') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_82269])).

tff(c_82558,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_9','#skF_11'),'#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11064,c_82366])).

tff(c_82760,plain,
    ( k1_xboole_0 = '#skF_12'
    | k4_xboole_0('#skF_9','#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_82558,c_74])).

tff(c_82786,plain,(
    k4_xboole_0('#skF_9','#skF_11') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52656,c_82760])).

tff(c_83013,plain,(
    ! [D_19] :
      ( r2_hidden(D_19,k1_xboole_0)
      | r2_hidden(D_19,'#skF_11')
      | ~ r2_hidden(D_19,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82786,c_28])).

tff(c_84489,plain,(
    ! [D_4321] :
      ( r2_hidden(D_4321,'#skF_11')
      | ~ r2_hidden(D_4321,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_83013])).

tff(c_85921,plain,(
    ! [A_4329] :
      ( r1_tarski(A_4329,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_4329,'#skF_11'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_84489,c_6])).

tff(c_85949,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_8,c_85921])).

tff(c_85959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58363,c_58363,c_85949])).

tff(c_85960,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_48265])).

tff(c_86018,plain,(
    ! [C_34] : ~ r2_hidden(C_34,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85960,c_221])).

tff(c_86022,plain,(
    ! [A_35] : k2_zfmisc_1(A_35,'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85960,c_85960,c_76])).

tff(c_87207,plain,(
    ! [A_3314] : r2_hidden('#skF_5'(A_3314,A_3314,k2_zfmisc_1('#skF_9','#skF_10')),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86022,c_24004])).

tff(c_87242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86018,c_87207])).

tff(c_87243,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_87245,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_87243])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_87272,plain,(
    '#skF_9' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87245,c_86])).

tff(c_87271,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87245,c_84])).

tff(c_87244,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_87277,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87245,c_87244])).

tff(c_87560,plain,(
    ! [B_4375,A_4376] :
      ( B_4375 = '#skF_12'
      | A_4376 = '#skF_12'
      | k2_zfmisc_1(A_4376,B_4375) != '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87245,c_87245,c_87245,c_74])).

tff(c_87569,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_9' = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_87277,c_87560])).

tff(c_87577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87272,c_87271,c_87569])).

tff(c_87578,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_87243])).

tff(c_87584,plain,(
    '#skF_11' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87578,c_84])).

tff(c_87591,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87578,c_87244])).

tff(c_87895,plain,(
    ! [B_4412,A_4413] :
      ( B_4412 = '#skF_11'
      | A_4413 = '#skF_11'
      | k2_zfmisc_1(A_4413,B_4412) != '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87578,c_87578,c_87578,c_74])).

tff(c_87904,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_11' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_87591,c_87895])).

tff(c_87912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_87584,c_87904])).

tff(c_87913,plain,(
    '#skF_10' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_88045,plain,(
    ! [D_4436,B_4437,A_4438] :
      ( ~ r2_hidden(D_4436,B_4437)
      | ~ r2_hidden(D_4436,k4_xboole_0(A_4438,B_4437)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88049,plain,(
    ! [D_4439,A_4440] :
      ( ~ r2_hidden(D_4439,A_4440)
      | ~ r2_hidden(D_4439,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_88045])).

tff(c_88052,plain,(
    ! [C_34] : ~ r2_hidden(C_34,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64,c_88049])).

tff(c_95959,plain,(
    ! [A_7675,B_7676,C_7677] :
      ( r2_hidden('#skF_2'(A_7675,B_7676,C_7677),B_7676)
      | r2_hidden('#skF_3'(A_7675,B_7676,C_7677),C_7677)
      | k3_xboole_0(A_7675,B_7676) = C_7677 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_128755,plain,(
    ! [A_8244,B_8245,A_8246,B_8247] :
      ( r2_hidden('#skF_3'(A_8244,B_8245,k4_xboole_0(A_8246,B_8247)),A_8246)
      | r2_hidden('#skF_2'(A_8244,B_8245,k4_xboole_0(A_8246,B_8247)),B_8245)
      | k4_xboole_0(A_8246,B_8247) = k3_xboole_0(A_8244,B_8245) ) ),
    inference(resolution,[status(thm)],[c_95959,c_32])).

tff(c_128869,plain,(
    ! [A_8244,B_8245,A_29] :
      ( r2_hidden('#skF_3'(A_8244,B_8245,k4_xboole_0(k1_xboole_0,A_29)),k1_xboole_0)
      | r2_hidden('#skF_2'(A_8244,B_8245,k1_xboole_0),B_8245)
      | k4_xboole_0(k1_xboole_0,A_29) = k3_xboole_0(A_8244,B_8245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_128755])).

tff(c_128899,plain,(
    ! [A_8244,B_8245] :
      ( r2_hidden('#skF_3'(A_8244,B_8245,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_2'(A_8244,B_8245,k1_xboole_0),B_8245)
      | k3_xboole_0(A_8244,B_8245) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_128869])).

tff(c_128900,plain,(
    ! [A_8244,B_8245] :
      ( r2_hidden('#skF_2'(A_8244,B_8245,k1_xboole_0),B_8245)
      | k3_xboole_0(A_8244,B_8245) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_88052,c_128899])).

tff(c_95617,plain,(
    ! [A_7654,B_7655,C_7656] :
      ( r2_hidden('#skF_2'(A_7654,B_7655,C_7656),A_7654)
      | r2_hidden('#skF_3'(A_7654,B_7655,C_7656),C_7656)
      | k3_xboole_0(A_7654,B_7655) = C_7656 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135847,plain,(
    ! [A_8342,B_8343,B_8344,C_8345] :
      ( ~ r2_hidden('#skF_2'(k4_xboole_0(A_8342,B_8343),B_8344,C_8345),B_8343)
      | r2_hidden('#skF_3'(k4_xboole_0(A_8342,B_8343),B_8344,C_8345),C_8345)
      | k3_xboole_0(k4_xboole_0(A_8342,B_8343),B_8344) = C_8345 ) ),
    inference(resolution,[status(thm)],[c_95617,c_30])).

tff(c_135861,plain,(
    ! [A_8342,B_8245] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_8342,B_8245),B_8245,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(k4_xboole_0(A_8342,B_8245),B_8245) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_128900,c_135847])).

tff(c_135914,plain,(
    ! [A_8342,B_8245] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_8342,B_8245),B_8245,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(B_8245,k4_xboole_0(A_8342,B_8245)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_135861])).

tff(c_135936,plain,(
    ! [B_8346,A_8347] : k3_xboole_0(B_8346,k4_xboole_0(A_8347,B_8346)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88052,c_135914])).

tff(c_87914,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_87919,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k2_zfmisc_1('#skF_9','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87914,c_88])).

tff(c_88773,plain,(
    ! [A_4507,C_4508,B_4509,D_4510] : k3_xboole_0(k2_zfmisc_1(A_4507,C_4508),k2_zfmisc_1(B_4509,D_4510)) = k2_zfmisc_1(k3_xboole_0(A_4507,B_4509),k3_xboole_0(C_4508,D_4510)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_88804,plain,(
    ! [A_4507,C_4508] : k3_xboole_0(k2_zfmisc_1(A_4507,C_4508),k2_zfmisc_1('#skF_9','#skF_12')) = k2_zfmisc_1(k3_xboole_0(A_4507,'#skF_9'),k3_xboole_0(C_4508,'#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_87919,c_88773])).

tff(c_96107,plain,(
    ! [A_7682,C_7683] : k2_zfmisc_1(k3_xboole_0(A_7682,'#skF_9'),k3_xboole_0(C_7683,'#skF_10')) = k2_zfmisc_1(k3_xboole_0(A_7682,'#skF_9'),k3_xboole_0(C_7683,'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_88804])).

tff(c_96150,plain,(
    ! [C_7683] : k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_9'),k3_xboole_0(C_7683,'#skF_12')) = k2_zfmisc_1('#skF_9',k3_xboole_0(C_7683,'#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_96107])).

tff(c_96163,plain,(
    ! [C_7684] : k2_zfmisc_1('#skF_9',k3_xboole_0(C_7684,'#skF_10')) = k2_zfmisc_1('#skF_9',k3_xboole_0(C_7684,'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_96150])).

tff(c_96175,plain,(
    ! [C_7684] :
      ( k3_xboole_0(C_7684,'#skF_10') = k1_xboole_0
      | k1_xboole_0 = '#skF_9'
      | k2_zfmisc_1('#skF_9',k3_xboole_0(C_7684,'#skF_12')) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96163,c_74])).

tff(c_96241,plain,(
    ! [C_7686] :
      ( k3_xboole_0(C_7686,'#skF_10') = k1_xboole_0
      | k2_zfmisc_1('#skF_9',k3_xboole_0(C_7686,'#skF_12')) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_96175])).

tff(c_96253,plain,(
    ! [B_2] :
      ( k3_xboole_0(B_2,'#skF_10') = k1_xboole_0
      | k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_12',B_2)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96241])).

tff(c_136431,plain,(
    ! [A_8347] :
      ( k3_xboole_0(k4_xboole_0(A_8347,'#skF_12'),'#skF_10') = k1_xboole_0
      | k2_zfmisc_1('#skF_9',k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135936,c_96253])).

tff(c_137452,plain,(
    ! [A_8350] : k3_xboole_0('#skF_10',k4_xboole_0(A_8350,'#skF_12')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2,c_136431])).

tff(c_88061,plain,(
    ! [A_4449,B_4450] :
      ( r2_hidden('#skF_1'(A_4449,B_4450),A_4449)
      | r1_tarski(A_4449,B_4450) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102027,plain,(
    ! [A_7847,B_7848,B_7849] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_7847,B_7848),B_7849),A_7847)
      | r1_tarski(k4_xboole_0(A_7847,B_7848),B_7849) ) ),
    inference(resolution,[status(thm)],[c_88061,c_32])).

tff(c_102082,plain,(
    ! [A_7850,B_7851] : r1_tarski(k4_xboole_0(A_7850,B_7851),A_7850) ),
    inference(resolution,[status(thm)],[c_102027,c_6])).

tff(c_102139,plain,(
    ! [A_7852,B_7853] : k3_xboole_0(k4_xboole_0(A_7852,B_7853),A_7852) = k4_xboole_0(A_7852,B_7853) ),
    inference(resolution,[status(thm)],[c_102082,c_58])).

tff(c_102311,plain,(
    ! [A_7852,B_7853] : k3_xboole_0(A_7852,k4_xboole_0(A_7852,B_7853)) = k4_xboole_0(A_7852,B_7853) ),
    inference(superposition,[status(thm),theory(equality)],[c_102139,c_2])).

tff(c_137734,plain,(
    k4_xboole_0('#skF_10','#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_137452,c_102311])).

tff(c_138162,plain,(
    ! [D_19] :
      ( r2_hidden(D_19,k1_xboole_0)
      | r2_hidden(D_19,'#skF_12')
      | ~ r2_hidden(D_19,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137734,c_28])).

tff(c_139037,plain,(
    ! [D_8357] :
      ( r2_hidden(D_8357,'#skF_12')
      | ~ r2_hidden(D_8357,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88052,c_138162])).

tff(c_145578,plain,(
    ! [B_8429] :
      ( r2_hidden('#skF_1'('#skF_10',B_8429),'#skF_12')
      | r1_tarski('#skF_10',B_8429) ) ),
    inference(resolution,[status(thm)],[c_8,c_139037])).

tff(c_145599,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_145578,c_6])).

tff(c_88238,plain,(
    ! [C_4458,B_4459,A_4460] :
      ( r2_hidden(C_4458,B_4459)
      | ~ r2_hidden(C_4458,A_4460)
      | ~ r1_tarski(A_4460,B_4459) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_88401,plain,(
    ! [A_4479,B_4480,B_4481] :
      ( r2_hidden('#skF_6'(A_4479,B_4480),B_4481)
      | ~ r1_tarski(B_4480,B_4481)
      | ~ r2_xboole_0(A_4479,B_4480) ) ),
    inference(resolution,[status(thm)],[c_56,c_88238])).

tff(c_88451,plain,(
    ! [B_4484,B_4485] :
      ( ~ r1_tarski(B_4484,B_4485)
      | ~ r2_xboole_0(B_4485,B_4484) ) ),
    inference(resolution,[status(thm)],[c_88401,c_54])).

tff(c_88455,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | B_21 = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_46,c_88451])).

tff(c_145604,plain,
    ( '#skF_10' = '#skF_12'
    | ~ r1_tarski('#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_145599,c_88455])).

tff(c_145611,plain,(
    ~ r1_tarski('#skF_12','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_87913,c_145604])).

tff(c_88091,plain,(
    ! [A_4449] : r1_tarski(A_4449,A_4449) ),
    inference(resolution,[status(thm)],[c_88061,c_6])).

tff(c_88246,plain,(
    ! [A_3,B_4,B_4459] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4459)
      | ~ r1_tarski(A_3,B_4459)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_88238])).

tff(c_96260,plain,(
    ! [A_7687] : k2_zfmisc_1('#skF_9',k3_xboole_0(A_7687,'#skF_12')) = k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_10',A_7687)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96163])).

tff(c_96321,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_10',B_2)) = k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_12',B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96260])).

tff(c_136423,plain,(
    ! [A_8347] : k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_12',k4_xboole_0(A_8347,'#skF_10'))) = k2_zfmisc_1('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_135936,c_96321])).

tff(c_140520,plain,(
    ! [A_8374] : k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_12',k4_xboole_0(A_8374,'#skF_10'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_136423])).

tff(c_96295,plain,(
    ! [A_7687] :
      ( k3_xboole_0(A_7687,'#skF_12') = k1_xboole_0
      | k1_xboole_0 = '#skF_9'
      | k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_10',A_7687)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96260,c_74])).

tff(c_96336,plain,(
    ! [A_7687] :
      ( k3_xboole_0(A_7687,'#skF_12') = k1_xboole_0
      | k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_10',A_7687)) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_96295])).

tff(c_96779,plain,(
    ! [A_7687] :
      ( k3_xboole_0(A_7687,'#skF_12') = k1_xboole_0
      | k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_12',A_7687)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96321,c_96336])).

tff(c_140817,plain,(
    ! [A_8379] : k3_xboole_0(k4_xboole_0(A_8379,'#skF_10'),'#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_140520,c_96779])).

tff(c_102136,plain,(
    ! [A_7850,B_7851] : k3_xboole_0(k4_xboole_0(A_7850,B_7851),A_7850) = k4_xboole_0(A_7850,B_7851) ),
    inference(resolution,[status(thm)],[c_102082,c_58])).

tff(c_141124,plain,(
    k4_xboole_0('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_140817,c_102136])).

tff(c_141576,plain,(
    ! [D_19] :
      ( r2_hidden(D_19,k1_xboole_0)
      | r2_hidden(D_19,'#skF_10')
      | ~ r2_hidden(D_19,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141124,c_28])).

tff(c_141649,plain,(
    ! [D_19] :
      ( r2_hidden(D_19,'#skF_10')
      | ~ r2_hidden(D_19,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88052,c_141576])).

tff(c_100012,plain,(
    ! [A_7822,B_7823,B_7824] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_7822,B_7823),B_7824),B_7823)
      | r1_tarski(k3_xboole_0(A_7822,B_7823),B_7824) ) ),
    inference(resolution,[status(thm)],[c_88061,c_12])).

tff(c_100078,plain,(
    ! [A_7822,B_7823] : r1_tarski(k3_xboole_0(A_7822,B_7823),B_7823) ),
    inference(resolution,[status(thm)],[c_100012,c_6])).

tff(c_88245,plain,(
    ! [A_24,B_25,B_4459] :
      ( r2_hidden('#skF_6'(A_24,B_25),B_4459)
      | ~ r1_tarski(B_25,B_4459)
      | ~ r2_xboole_0(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_56,c_88238])).

tff(c_88362,plain,(
    ! [D_4476,A_4477,B_4478] :
      ( r2_hidden(D_4476,k3_xboole_0(A_4477,B_4478))
      | ~ r2_hidden(D_4476,B_4478)
      | ~ r2_hidden(D_4476,A_4477) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_119166,plain,(
    ! [A_8107,B_8108,B_8109] :
      ( ~ r2_xboole_0(k3_xboole_0(A_8107,B_8108),B_8109)
      | ~ r2_hidden('#skF_6'(k3_xboole_0(A_8107,B_8108),B_8109),B_8108)
      | ~ r2_hidden('#skF_6'(k3_xboole_0(A_8107,B_8108),B_8109),A_8107) ) ),
    inference(resolution,[status(thm)],[c_88362,c_54])).

tff(c_130163,plain,(
    ! [A_8264,B_8265] :
      ( ~ r2_hidden('#skF_6'(k3_xboole_0(A_8264,B_8265),B_8265),A_8264)
      | ~ r2_xboole_0(k3_xboole_0(A_8264,B_8265),B_8265) ) ),
    inference(resolution,[status(thm)],[c_56,c_119166])).

tff(c_130340,plain,(
    ! [B_8266,B_8267] :
      ( ~ r1_tarski(B_8266,B_8267)
      | ~ r2_xboole_0(k3_xboole_0(B_8267,B_8266),B_8266) ) ),
    inference(resolution,[status(thm)],[c_88245,c_130163])).

tff(c_130443,plain,(
    ! [B_21,B_8267] :
      ( ~ r1_tarski(B_21,B_8267)
      | k3_xboole_0(B_8267,B_21) = B_21
      | ~ r1_tarski(k3_xboole_0(B_8267,B_21),B_21) ) ),
    inference(resolution,[status(thm)],[c_46,c_130340])).

tff(c_130473,plain,(
    ! [B_21,B_8267] :
      ( ~ r1_tarski(B_21,B_8267)
      | k3_xboole_0(B_8267,B_21) = B_21 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100078,c_130443])).

tff(c_145608,plain,(
    k3_xboole_0('#skF_12','#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_145599,c_130473])).

tff(c_145612,plain,(
    k3_xboole_0('#skF_10','#skF_12') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_145599,c_58])).

tff(c_123207,plain,(
    ! [A_8160,A_8161,B_8162] :
      ( r1_tarski(A_8160,k3_xboole_0(A_8161,B_8162))
      | ~ r2_hidden('#skF_1'(A_8160,k3_xboole_0(A_8161,B_8162)),B_8162)
      | ~ r2_hidden('#skF_1'(A_8160,k3_xboole_0(A_8161,B_8162)),A_8161) ) ),
    inference(resolution,[status(thm)],[c_88362,c_6])).

tff(c_123327,plain,(
    ! [A_3,A_8161] :
      ( ~ r2_hidden('#skF_1'(A_3,k3_xboole_0(A_8161,A_3)),A_8161)
      | r1_tarski(A_3,k3_xboole_0(A_8161,A_3)) ) ),
    inference(resolution,[status(thm)],[c_8,c_123207])).

tff(c_146301,plain,
    ( ~ r2_hidden('#skF_1'('#skF_12','#skF_10'),'#skF_10')
    | r1_tarski('#skF_12',k3_xboole_0('#skF_10','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_145612,c_123327])).

tff(c_146714,plain,
    ( ~ r2_hidden('#skF_1'('#skF_12','#skF_10'),'#skF_10')
    | r1_tarski('#skF_12','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145608,c_2,c_146301])).

tff(c_146715,plain,(
    ~ r2_hidden('#skF_1'('#skF_12','#skF_10'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_145611,c_146714])).

tff(c_146830,plain,(
    ~ r2_hidden('#skF_1'('#skF_12','#skF_10'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_141649,c_146715])).

tff(c_146836,plain,
    ( ~ r1_tarski('#skF_12','#skF_12')
    | r1_tarski('#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_88246,c_146830])).

tff(c_146842,plain,(
    r1_tarski('#skF_12','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88091,c_146836])).

tff(c_146844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145611,c_146842])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:41:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.24/23.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.24/23.56  
% 36.24/23.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.24/23.56  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1 > #skF_12
% 36.24/23.56  
% 36.24/23.56  %Foreground sorts:
% 36.24/23.56  
% 36.24/23.56  
% 36.24/23.56  %Background operators:
% 36.24/23.56  
% 36.24/23.56  
% 36.24/23.56  %Foreground operators:
% 36.24/23.56  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 36.24/23.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.24/23.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.24/23.56  tff('#skF_11', type, '#skF_11': $i).
% 36.24/23.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 36.24/23.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 36.24/23.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.24/23.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 36.24/23.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.24/23.56  tff('#skF_10', type, '#skF_10': $i).
% 36.24/23.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 36.24/23.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 36.24/23.56  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 36.24/23.56  tff('#skF_9', type, '#skF_9': $i).
% 36.24/23.56  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 36.24/23.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.24/23.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 36.24/23.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 36.24/23.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.24/23.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.24/23.56  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 36.24/23.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 36.24/23.56  tff('#skF_12', type, '#skF_12': $i).
% 36.24/23.56  
% 36.57/23.60  tff(f_104, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 36.57/23.60  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 36.57/23.60  tff(f_85, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 36.57/23.60  tff(f_78, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 36.57/23.60  tff(f_53, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 36.57/23.60  tff(f_76, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 36.57/23.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 36.57/23.60  tff(f_91, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 36.57/23.60  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 36.57/23.60  tff(f_62, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 36.57/23.60  tff(f_93, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 36.57/23.60  tff(f_60, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 36.57/23.60  tff(f_72, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 36.57/23.60  tff(c_82, plain, ('#skF_10'!='#skF_12' | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_104])).
% 36.57/23.60  tff(c_99, plain, ('#skF_11'!='#skF_9'), inference(splitLeft, [status(thm)], [c_82])).
% 36.57/23.60  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.57/23.60  tff(c_64, plain, (![C_34]: (r2_hidden(C_34, k1_tarski(C_34)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 36.57/23.60  tff(c_60, plain, (![A_29]: (k4_xboole_0(k1_xboole_0, A_29)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 36.57/23.60  tff(c_214, plain, (![D_66, B_67, A_68]: (~r2_hidden(D_66, B_67) | ~r2_hidden(D_66, k4_xboole_0(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.57/23.60  tff(c_218, plain, (![D_69, A_70]: (~r2_hidden(D_69, A_70) | ~r2_hidden(D_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_214])).
% 36.57/23.60  tff(c_221, plain, (![C_34]: (~r2_hidden(C_34, k1_xboole_0))), inference(resolution, [status(thm)], [c_64, c_218])).
% 36.57/23.60  tff(c_278, plain, (![A_81, B_82]: (r2_hidden('#skF_1'(A_81, B_82), A_81) | r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.57/23.60  tff(c_32, plain, (![D_19, A_14, B_15]: (r2_hidden(D_19, A_14) | ~r2_hidden(D_19, k4_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.57/23.60  tff(c_10861, plain, (![A_3394, B_3395, B_3396]: (r2_hidden('#skF_1'(k4_xboole_0(A_3394, B_3395), B_3396), A_3394) | r1_tarski(k4_xboole_0(A_3394, B_3395), B_3396))), inference(resolution, [status(thm)], [c_278, c_32])).
% 36.57/23.60  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.57/23.60  tff(c_10910, plain, (![A_3397, B_3398]: (r1_tarski(k4_xboole_0(A_3397, B_3398), A_3397))), inference(resolution, [status(thm)], [c_10861, c_6])).
% 36.57/23.60  tff(c_58, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 36.57/23.60  tff(c_10966, plain, (![A_3399, B_3400]: (k3_xboole_0(k4_xboole_0(A_3399, B_3400), A_3399)=k4_xboole_0(A_3399, B_3400))), inference(resolution, [status(thm)], [c_10910, c_58])).
% 36.57/23.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.57/23.60  tff(c_11064, plain, (![A_3399, B_3400]: (k3_xboole_0(A_3399, k4_xboole_0(A_3399, B_3400))=k4_xboole_0(A_3399, B_3400))), inference(superposition, [status(thm), theory('equality')], [c_10966, c_2])).
% 36.57/23.60  tff(c_78, plain, (![B_36]: (k2_zfmisc_1(k1_xboole_0, B_36)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.57/23.60  tff(c_320, plain, (![B_84]: (r1_tarski(k1_xboole_0, B_84))), inference(resolution, [status(thm)], [c_278, c_221])).
% 36.57/23.60  tff(c_324, plain, (![B_84]: (k3_xboole_0(k1_xboole_0, B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_320, c_58])).
% 36.57/23.60  tff(c_325, plain, (![B_85]: (k3_xboole_0(k1_xboole_0, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_320, c_58])).
% 36.57/23.60  tff(c_336, plain, (![B_85]: (k3_xboole_0(B_85, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_325, c_2])).
% 36.57/23.60  tff(c_8031, plain, (![A_3292, B_3293, C_3294]: (r2_hidden('#skF_2'(A_3292, B_3293, C_3294), A_3292) | r2_hidden('#skF_3'(A_3292, B_3293, C_3294), C_3294) | k3_xboole_0(A_3292, B_3293)=C_3294)), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.57/23.60  tff(c_12, plain, (![D_13, B_9, A_8]: (r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.57/23.60  tff(c_37187, plain, (![A_3832, B_3833, A_3834, B_3835]: (r2_hidden('#skF_3'(A_3832, B_3833, k3_xboole_0(A_3834, B_3835)), B_3835) | r2_hidden('#skF_2'(A_3832, B_3833, k3_xboole_0(A_3834, B_3835)), A_3832) | k3_xboole_0(A_3834, B_3835)=k3_xboole_0(A_3832, B_3833))), inference(resolution, [status(thm)], [c_8031, c_12])).
% 36.57/23.60  tff(c_37460, plain, (![A_3832, B_3833, B_85]: (r2_hidden('#skF_3'(A_3832, B_3833, k3_xboole_0(B_85, k1_xboole_0)), k1_xboole_0) | r2_hidden('#skF_2'(A_3832, B_3833, k1_xboole_0), A_3832) | k3_xboole_0(B_85, k1_xboole_0)=k3_xboole_0(A_3832, B_3833))), inference(superposition, [status(thm), theory('equality')], [c_336, c_37187])).
% 36.57/23.60  tff(c_37554, plain, (![A_3832, B_3833]: (r2_hidden('#skF_3'(A_3832, B_3833, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_2'(A_3832, B_3833, k1_xboole_0), A_3832) | k3_xboole_0(A_3832, B_3833)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_336, c_336, c_37460])).
% 36.57/23.60  tff(c_37555, plain, (![A_3832, B_3833]: (r2_hidden('#skF_2'(A_3832, B_3833, k1_xboole_0), A_3832) | k3_xboole_0(A_3832, B_3833)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_221, c_37554])).
% 36.57/23.60  tff(c_7576, plain, (![A_3266, B_3267, C_3268]: (r2_hidden('#skF_2'(A_3266, B_3267, C_3268), B_3267) | r2_hidden('#skF_3'(A_3266, B_3267, C_3268), C_3268) | k3_xboole_0(A_3266, B_3267)=C_3268)), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.57/23.60  tff(c_30, plain, (![D_19, B_15, A_14]: (~r2_hidden(D_19, B_15) | ~r2_hidden(D_19, k4_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.57/23.60  tff(c_42903, plain, (![A_3892, A_3893, B_3894, C_3895]: (~r2_hidden('#skF_2'(A_3892, k4_xboole_0(A_3893, B_3894), C_3895), B_3894) | r2_hidden('#skF_3'(A_3892, k4_xboole_0(A_3893, B_3894), C_3895), C_3895) | k3_xboole_0(A_3892, k4_xboole_0(A_3893, B_3894))=C_3895)), inference(resolution, [status(thm)], [c_7576, c_30])).
% 36.57/23.60  tff(c_42912, plain, (![A_3832, A_3893]: (r2_hidden('#skF_3'(A_3832, k4_xboole_0(A_3893, A_3832), k1_xboole_0), k1_xboole_0) | k3_xboole_0(A_3832, k4_xboole_0(A_3893, A_3832))=k1_xboole_0)), inference(resolution, [status(thm)], [c_37555, c_42903])).
% 36.57/23.60  tff(c_42976, plain, (![A_3896, A_3897]: (k3_xboole_0(A_3896, k4_xboole_0(A_3897, A_3896))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_221, c_42912])).
% 36.57/23.60  tff(c_9785, plain, (![A_3374, B_3375, B_3376]: (r2_hidden('#skF_1'(k3_xboole_0(A_3374, B_3375), B_3376), B_3375) | r1_tarski(k3_xboole_0(A_3374, B_3375), B_3376))), inference(resolution, [status(thm)], [c_278, c_12])).
% 36.57/23.60  tff(c_9857, plain, (![A_3377, B_3378]: (r1_tarski(k3_xboole_0(A_3377, B_3378), B_3378))), inference(resolution, [status(thm)], [c_9785, c_6])).
% 36.57/23.60  tff(c_9937, plain, (![B_3379, A_3380]: (r1_tarski(k3_xboole_0(B_3379, A_3380), B_3379))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9857])).
% 36.57/23.60  tff(c_10231, plain, (![B_3386, A_3387]: (k3_xboole_0(k3_xboole_0(B_3386, A_3387), B_3386)=k3_xboole_0(B_3386, A_3387))), inference(resolution, [status(thm)], [c_9937, c_58])).
% 36.57/23.60  tff(c_11786, plain, (![B_3412, A_3413]: (k3_xboole_0(k3_xboole_0(B_3412, A_3413), A_3413)=k3_xboole_0(A_3413, B_3412))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10231])).
% 36.57/23.60  tff(c_11981, plain, (![B_2, B_3412]: (k3_xboole_0(B_2, k3_xboole_0(B_3412, B_2))=k3_xboole_0(B_2, B_3412))), inference(superposition, [status(thm), theory('equality')], [c_2, c_11786])).
% 36.57/23.60  tff(c_43388, plain, (![A_3897, A_3896]: (k3_xboole_0(k4_xboole_0(A_3897, A_3896), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_3897, A_3896), A_3896))), inference(superposition, [status(thm), theory('equality')], [c_42976, c_11981])).
% 36.57/23.60  tff(c_43685, plain, (![A_3898, A_3899]: (k3_xboole_0(k4_xboole_0(A_3898, A_3899), A_3899)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_324, c_2, c_43388])).
% 36.57/23.60  tff(c_52, plain, (![A_22]: (k3_xboole_0(A_22, A_22)=A_22)), inference(cnfTransformation, [status(thm)], [f_62])).
% 36.57/23.60  tff(c_80, plain, (![A_37, C_39, B_38, D_40]: (k3_xboole_0(k2_zfmisc_1(A_37, C_39), k2_zfmisc_1(B_38, D_40))=k2_zfmisc_1(k3_xboole_0(A_37, B_38), k3_xboole_0(C_39, D_40)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 36.57/23.60  tff(c_88, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_104])).
% 36.57/23.60  tff(c_6912, plain, (![A_3204, C_3205, B_3206, D_3207]: (k3_xboole_0(k2_zfmisc_1(A_3204, C_3205), k2_zfmisc_1(B_3206, D_3207))=k2_zfmisc_1(k3_xboole_0(A_3204, B_3206), k3_xboole_0(C_3205, D_3207)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 36.57/23.60  tff(c_7471, plain, (![A_3204, C_3205]: (k3_xboole_0(k2_zfmisc_1(A_3204, C_3205), k2_zfmisc_1('#skF_9', '#skF_10'))=k2_zfmisc_1(k3_xboole_0(A_3204, '#skF_11'), k3_xboole_0(C_3205, '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_88, c_6912])).
% 36.57/23.60  tff(c_7683, plain, (![A_3271, C_3272]: (k2_zfmisc_1(k3_xboole_0(A_3271, '#skF_11'), k3_xboole_0(C_3272, '#skF_12'))=k2_zfmisc_1(k3_xboole_0(A_3271, '#skF_9'), k3_xboole_0(C_3272, '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_7471])).
% 36.57/23.60  tff(c_7730, plain, (![A_3271]: (k2_zfmisc_1(k3_xboole_0(A_3271, '#skF_9'), k3_xboole_0('#skF_12', '#skF_10'))=k2_zfmisc_1(k3_xboole_0(A_3271, '#skF_11'), '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_7683])).
% 36.57/23.60  tff(c_44182, plain, (![A_3898]: (k2_zfmisc_1(k3_xboole_0(k4_xboole_0(A_3898, '#skF_9'), '#skF_11'), '#skF_12')=k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_12', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_43685, c_7730])).
% 36.57/23.60  tff(c_47643, plain, (![A_3921]: (k2_zfmisc_1(k3_xboole_0('#skF_11', k4_xboole_0(A_3921, '#skF_9')), '#skF_12')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_78, c_44182])).
% 36.57/23.60  tff(c_47839, plain, (k2_zfmisc_1(k4_xboole_0('#skF_11', '#skF_9'), '#skF_12')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11064, c_47643])).
% 36.57/23.60  tff(c_74, plain, (![B_36, A_35]: (k1_xboole_0=B_36 | k1_xboole_0=A_35 | k2_zfmisc_1(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.57/23.60  tff(c_48265, plain, (k1_xboole_0='#skF_12' | k4_xboole_0('#skF_11', '#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_47839, c_74])).
% 36.57/23.60  tff(c_48267, plain, (k4_xboole_0('#skF_11', '#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48265])).
% 36.57/23.60  tff(c_28, plain, (![D_19, A_14, B_15]: (r2_hidden(D_19, k4_xboole_0(A_14, B_15)) | r2_hidden(D_19, B_15) | ~r2_hidden(D_19, A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.57/23.60  tff(c_48429, plain, (![D_19]: (r2_hidden(D_19, k1_xboole_0) | r2_hidden(D_19, '#skF_9') | ~r2_hidden(D_19, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_48267, c_28])).
% 36.57/23.60  tff(c_48499, plain, (![D_3926]: (r2_hidden(D_3926, '#skF_9') | ~r2_hidden(D_3926, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_221, c_48429])).
% 36.57/23.60  tff(c_58339, plain, (![B_4009]: (r2_hidden('#skF_1'('#skF_11', B_4009), '#skF_9') | r1_tarski('#skF_11', B_4009))), inference(resolution, [status(thm)], [c_8, c_48499])).
% 36.57/23.60  tff(c_58355, plain, (r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_58339, c_6])).
% 36.57/23.60  tff(c_46, plain, (![A_20, B_21]: (r2_xboole_0(A_20, B_21) | B_21=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 36.57/23.60  tff(c_56, plain, (![A_24, B_25]: (r2_hidden('#skF_6'(A_24, B_25), B_25) | ~r2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 36.57/23.60  tff(c_414, plain, (![C_87, B_88, A_89]: (r2_hidden(C_87, B_88) | ~r2_hidden(C_87, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.57/23.60  tff(c_587, plain, (![A_110, B_111, B_112]: (r2_hidden('#skF_6'(A_110, B_111), B_112) | ~r1_tarski(B_111, B_112) | ~r2_xboole_0(A_110, B_111))), inference(resolution, [status(thm)], [c_56, c_414])).
% 36.57/23.60  tff(c_54, plain, (![A_24, B_25]: (~r2_hidden('#skF_6'(A_24, B_25), A_24) | ~r2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 36.57/23.60  tff(c_626, plain, (![B_113, B_114]: (~r1_tarski(B_113, B_114) | ~r2_xboole_0(B_114, B_113))), inference(resolution, [status(thm)], [c_587, c_54])).
% 36.57/23.60  tff(c_630, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | B_21=A_20 | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_46, c_626])).
% 36.57/23.60  tff(c_58357, plain, ('#skF_11'='#skF_9' | ~r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_58355, c_630])).
% 36.57/23.60  tff(c_58363, plain, (~r1_tarski('#skF_9', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_99, c_58357])).
% 36.57/23.60  tff(c_47872, plain, (![A_3921]: (k1_xboole_0='#skF_12' | k3_xboole_0('#skF_11', k4_xboole_0(A_3921, '#skF_9'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_47643, c_74])).
% 36.57/23.60  tff(c_49834, plain, (k1_xboole_0='#skF_12'), inference(splitLeft, [status(thm)], [c_47872])).
% 36.57/23.60  tff(c_49896, plain, (![C_34]: (~r2_hidden(C_34, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_49834, c_221])).
% 36.57/23.60  tff(c_76, plain, (![A_35]: (k2_zfmisc_1(A_35, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.57/23.60  tff(c_49900, plain, (![A_35]: (k2_zfmisc_1(A_35, '#skF_12')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_49834, c_49834, c_76])).
% 36.57/23.60  tff(c_175, plain, (![B_55, A_56]: (k1_xboole_0=B_55 | k1_xboole_0=A_56 | k2_zfmisc_1(A_56, B_55)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.57/23.60  tff(c_181, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_88, c_175])).
% 36.57/23.60  tff(c_213, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_181])).
% 36.57/23.60  tff(c_8407, plain, (![A_3314, B_3315, C_3316]: (r2_hidden('#skF_4'(A_3314, B_3315, C_3316), A_3314) | r2_hidden('#skF_5'(A_3314, B_3315, C_3316), C_3316) | k4_xboole_0(A_3314, B_3315)=C_3316)), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.57/23.60  tff(c_42, plain, (![A_14, B_15, C_16]: (~r2_hidden('#skF_4'(A_14, B_15, C_16), B_15) | r2_hidden('#skF_5'(A_14, B_15, C_16), C_16) | k4_xboole_0(A_14, B_15)=C_16)), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.57/23.60  tff(c_8535, plain, (![A_3321, C_3322]: (r2_hidden('#skF_5'(A_3321, A_3321, C_3322), C_3322) | k4_xboole_0(A_3321, A_3321)=C_3322)), inference(resolution, [status(thm)], [c_8407, c_42])).
% 36.57/23.60  tff(c_8567, plain, (![A_3321]: (k4_xboole_0(A_3321, A_3321)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8535, c_221])).
% 36.57/23.60  tff(c_8465, plain, (![A_3314, C_3316]: (r2_hidden('#skF_5'(A_3314, A_3314, C_3316), C_3316) | k4_xboole_0(A_3314, A_3314)=C_3316)), inference(resolution, [status(thm)], [c_8407, c_42])).
% 36.57/23.60  tff(c_8626, plain, (![A_3314, C_3316]: (r2_hidden('#skF_5'(A_3314, A_3314, C_3316), C_3316) | k1_xboole_0=C_3316)), inference(demodulation, [status(thm), theory('equality')], [c_8567, c_8465])).
% 36.57/23.60  tff(c_14824, plain, (![B_3477, D_3478, A_3479, C_3480]: (k3_xboole_0(k2_zfmisc_1(B_3477, D_3478), k2_zfmisc_1(A_3479, C_3480))=k2_zfmisc_1(k3_xboole_0(A_3479, B_3477), k3_xboole_0(C_3480, D_3478)))), inference(superposition, [status(thm), theory('equality')], [c_6912, c_2])).
% 36.57/23.60  tff(c_9844, plain, (![A_3374, B_3375]: (r1_tarski(k3_xboole_0(A_3374, B_3375), B_3375))), inference(resolution, [status(thm)], [c_9785, c_6])).
% 36.57/23.60  tff(c_17710, plain, (![A_3532, B_3533, C_3534, D_3535]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_3532, B_3533), k3_xboole_0(C_3534, D_3535)), k2_zfmisc_1(A_3532, C_3534)))), inference(superposition, [status(thm), theory('equality')], [c_14824, c_9844])).
% 36.57/23.60  tff(c_18107, plain, (![A_3541, C_3542, D_3543]: (r1_tarski(k2_zfmisc_1(A_3541, k3_xboole_0(C_3542, D_3543)), k2_zfmisc_1(A_3541, C_3542)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_17710])).
% 36.57/23.60  tff(c_18256, plain, (![A_3541, A_1, B_2]: (r1_tarski(k2_zfmisc_1(A_3541, k3_xboole_0(A_1, B_2)), k2_zfmisc_1(A_3541, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_18107])).
% 36.57/23.60  tff(c_7468, plain, (![B_3206, D_3207]: (k3_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1(B_3206, D_3207))=k2_zfmisc_1(k3_xboole_0('#skF_11', B_3206), k3_xboole_0('#skF_12', D_3207)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_6912])).
% 36.57/23.60  tff(c_7809, plain, (![B_3280, D_3281]: (k2_zfmisc_1(k3_xboole_0('#skF_11', B_3280), k3_xboole_0('#skF_12', D_3281))=k2_zfmisc_1(k3_xboole_0('#skF_9', B_3280), k3_xboole_0('#skF_10', D_3281)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_7468])).
% 36.57/23.60  tff(c_8337, plain, (![D_3313]: (k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), k3_xboole_0('#skF_10', D_3313))=k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', D_3313)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_7809])).
% 36.57/23.60  tff(c_8380, plain, (k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), '#skF_10')=k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_8337])).
% 36.57/23.60  tff(c_7844, plain, (![B_2, D_3281]: (k2_zfmisc_1(k3_xboole_0(B_2, '#skF_11'), k3_xboole_0('#skF_12', D_3281))=k2_zfmisc_1(k3_xboole_0('#skF_9', B_2), k3_xboole_0('#skF_10', D_3281)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7809])).
% 36.57/23.60  tff(c_19647, plain, (![A_3576, B_3577, C_3578, D_3579]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_3576, B_3577), k3_xboole_0(C_3578, D_3579)), k2_zfmisc_1(B_3577, D_3579)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_9857])).
% 36.57/23.60  tff(c_20270, plain, (![B_3589, D_3590]: (r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_9', B_3589), k3_xboole_0('#skF_10', D_3590)), k2_zfmisc_1('#skF_11', D_3590)))), inference(superposition, [status(thm), theory('equality')], [c_7844, c_19647])).
% 36.57/23.60  tff(c_20386, plain, (![D_3591]: (r1_tarski(k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_10', D_3591)), k2_zfmisc_1('#skF_11', D_3591)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_20270])).
% 36.57/23.60  tff(c_20438, plain, (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_20386])).
% 36.57/23.60  tff(c_20450, plain, (k3_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_10'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_20438, c_58])).
% 36.57/23.60  tff(c_6930, plain, (![B_3206, D_3207, A_3204, C_3205]: (k3_xboole_0(k2_zfmisc_1(B_3206, D_3207), k2_zfmisc_1(A_3204, C_3205))=k2_zfmisc_1(k3_xboole_0(A_3204, B_3206), k3_xboole_0(C_3205, D_3207)))), inference(superposition, [status(thm), theory('equality')], [c_6912, c_2])).
% 36.57/23.60  tff(c_20922, plain, (k2_zfmisc_1(k3_xboole_0('#skF_11', '#skF_9'), k3_xboole_0('#skF_10', '#skF_10'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_20450, c_6930])).
% 36.57/23.60  tff(c_21043, plain, (k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', '#skF_10'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_8380, c_2, c_52, c_20922])).
% 36.57/23.60  tff(c_21082, plain, (k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), '#skF_10')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_21043, c_8380])).
% 36.57/23.60  tff(c_10011, plain, (![B_3379, A_3380]: (k3_xboole_0(k3_xboole_0(B_3379, A_3380), B_3379)=k3_xboole_0(B_3379, A_3380))), inference(resolution, [status(thm)], [c_9937, c_58])).
% 36.57/23.60  tff(c_10234, plain, (![B_3386, A_3387]: (k3_xboole_0(k3_xboole_0(B_3386, A_3387), k3_xboole_0(B_3386, A_3387))=k3_xboole_0(k3_xboole_0(B_3386, A_3387), B_3386))), inference(superposition, [status(thm), theory('equality')], [c_10231, c_10011])).
% 36.57/23.60  tff(c_10381, plain, (![B_3386, A_3387]: (k3_xboole_0(B_3386, k3_xboole_0(B_3386, A_3387))=k3_xboole_0(B_3386, A_3387))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52, c_10234])).
% 36.57/23.60  tff(c_8574, plain, (![A_3323]: (k2_zfmisc_1(k3_xboole_0(A_3323, '#skF_9'), k3_xboole_0('#skF_12', '#skF_10'))=k2_zfmisc_1(k3_xboole_0(A_3323, '#skF_11'), '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_7683])).
% 36.57/23.60  tff(c_8617, plain, (k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), '#skF_12')=k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_12', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_8574])).
% 36.57/23.60  tff(c_7714, plain, (![A_3271, A_1]: (k2_zfmisc_1(k3_xboole_0(A_3271, '#skF_11'), k3_xboole_0('#skF_12', A_1))=k2_zfmisc_1(k3_xboole_0(A_3271, '#skF_9'), k3_xboole_0(A_1, '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7683])).
% 36.57/23.60  tff(c_223, plain, (![A_72, B_73]: (r2_hidden('#skF_6'(A_72, B_73), B_73) | ~r2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_72])).
% 36.57/23.60  tff(c_12786, plain, (![A_3435, A_3436, B_3437]: (r2_hidden('#skF_6'(A_3435, k3_xboole_0(A_3436, B_3437)), B_3437) | ~r2_xboole_0(A_3435, k3_xboole_0(A_3436, B_3437)))), inference(resolution, [status(thm)], [c_223, c_12])).
% 36.57/23.60  tff(c_12875, plain, (![B_3437, A_3436]: (~r2_xboole_0(B_3437, k3_xboole_0(A_3436, B_3437)))), inference(resolution, [status(thm)], [c_12786, c_54])).
% 36.57/23.60  tff(c_17466, plain, (![A_3528, C_3529, B_3530, D_3531]: (~r2_xboole_0(k2_zfmisc_1(A_3528, C_3529), k2_zfmisc_1(k3_xboole_0(A_3528, B_3530), k3_xboole_0(C_3529, D_3531))))), inference(superposition, [status(thm), theory('equality')], [c_14824, c_12875])).
% 36.57/23.60  tff(c_22642, plain, (![A_3615, A_3616]: (~r2_xboole_0(k2_zfmisc_1(A_3615, '#skF_12'), k2_zfmisc_1(k3_xboole_0(A_3615, '#skF_9'), k3_xboole_0(A_3616, '#skF_10'))))), inference(superposition, [status(thm), theory('equality')], [c_7714, c_17466])).
% 36.57/23.60  tff(c_22825, plain, (![A_3618]: (~r2_xboole_0(k2_zfmisc_1(A_3618, '#skF_12'), k2_zfmisc_1(k3_xboole_0(A_3618, '#skF_9'), '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_22642])).
% 36.57/23.60  tff(c_22861, plain, (~r2_xboole_0(k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_12', '#skF_10')), k2_zfmisc_1(k3_xboole_0(k3_xboole_0('#skF_9', '#skF_11'), '#skF_9'), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_8617, c_22825])).
% 36.57/23.60  tff(c_22895, plain, (~r2_xboole_0(k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_12', '#skF_10')), k2_zfmisc_1('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_21082, c_10381, c_2, c_22861])).
% 36.57/23.60  tff(c_23229, plain, (k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_12', '#skF_10'))=k2_zfmisc_1('#skF_9', '#skF_10') | ~r1_tarski(k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_12', '#skF_10')), k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_46, c_22895])).
% 36.57/23.60  tff(c_23232, plain, (k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_12', '#skF_10'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_18256, c_23229])).
% 36.57/23.60  tff(c_17937, plain, (![A_22, C_3534, D_3535]: (r1_tarski(k2_zfmisc_1(A_22, k3_xboole_0(C_3534, D_3535)), k2_zfmisc_1(A_22, C_3534)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_17710])).
% 36.57/23.60  tff(c_23264, plain, (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_9', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_23232, c_17937])).
% 36.57/23.60  tff(c_23391, plain, (k3_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_9', '#skF_12'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_23264, c_58])).
% 36.57/23.60  tff(c_23806, plain, (![D_3633]: (r2_hidden(D_3633, k2_zfmisc_1('#skF_9', '#skF_12')) | ~r2_hidden(D_3633, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_23391, c_12])).
% 36.57/23.60  tff(c_23902, plain, (![A_3314]: (r2_hidden('#skF_5'(A_3314, A_3314, k2_zfmisc_1('#skF_9', '#skF_10')), k2_zfmisc_1('#skF_9', '#skF_12')) | k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0)), inference(resolution, [status(thm)], [c_8626, c_23806])).
% 36.57/23.60  tff(c_24004, plain, (![A_3314]: (r2_hidden('#skF_5'(A_3314, A_3314, k2_zfmisc_1('#skF_9', '#skF_10')), k2_zfmisc_1('#skF_9', '#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_213, c_23902])).
% 36.57/23.60  tff(c_52622, plain, (![A_3314]: (r2_hidden('#skF_5'(A_3314, A_3314, k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_49900, c_24004])).
% 36.57/23.60  tff(c_52654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49896, c_52622])).
% 36.57/23.60  tff(c_52656, plain, (k1_xboole_0!='#skF_12'), inference(splitRight, [status(thm)], [c_47872])).
% 36.57/23.60  tff(c_42961, plain, (![A_3832, A_3893]: (k3_xboole_0(A_3832, k4_xboole_0(A_3893, A_3832))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_221, c_42912])).
% 36.57/23.60  tff(c_7860, plain, (![D_3281]: (k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), k3_xboole_0('#skF_10', D_3281))=k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', D_3281)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_7809])).
% 36.57/23.60  tff(c_43455, plain, (![A_3897]: (k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', k4_xboole_0(A_3897, '#skF_10')))=k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42976, c_7860])).
% 36.57/23.60  tff(c_44439, plain, (![A_3900]: (k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', k4_xboole_0(A_3900, '#skF_10')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_43455])).
% 36.57/23.60  tff(c_44636, plain, (k2_zfmisc_1('#skF_11', k4_xboole_0('#skF_12', '#skF_10'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11064, c_44439])).
% 36.57/23.60  tff(c_44859, plain, (k4_xboole_0('#skF_12', '#skF_10')=k1_xboole_0 | k1_xboole_0='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_44636, c_74])).
% 36.57/23.60  tff(c_44861, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_44859])).
% 36.57/23.60  tff(c_44967, plain, (![B_36]: (k2_zfmisc_1('#skF_11', B_36)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_44861, c_44861, c_78])).
% 36.57/23.60  tff(c_45370, plain, (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_44967, c_88])).
% 36.57/23.60  tff(c_84, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_104])).
% 36.57/23.60  tff(c_7509, plain, (![B_3206, D_3207]: (k2_zfmisc_1(k3_xboole_0('#skF_11', B_3206), k3_xboole_0('#skF_12', D_3207))=k2_zfmisc_1(k3_xboole_0('#skF_9', B_3206), k3_xboole_0('#skF_10', D_3207)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_7468])).
% 36.57/23.60  tff(c_9225, plain, (![B_3359, C_3360]: (k2_zfmisc_1(k3_xboole_0(B_3359, '#skF_9'), k3_xboole_0(C_3360, '#skF_10'))=k2_zfmisc_1(k3_xboole_0('#skF_11', B_3359), k3_xboole_0(C_3360, '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7683])).
% 36.57/23.60  tff(c_9352, plain, (![B_3359]: (k2_zfmisc_1(k3_xboole_0('#skF_11', B_3359), k3_xboole_0('#skF_10', '#skF_12'))=k2_zfmisc_1(k3_xboole_0(B_3359, '#skF_9'), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_9225])).
% 36.57/23.60  tff(c_9450, plain, (![B_3362]: (k2_zfmisc_1(k3_xboole_0(B_3362, '#skF_9'), '#skF_10')=k2_zfmisc_1(k3_xboole_0('#skF_9', B_3362), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_7509, c_2, c_9352])).
% 36.57/23.60  tff(c_9471, plain, (![B_3362]: (k1_xboole_0='#skF_10' | k3_xboole_0('#skF_9', B_3362)=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0(B_3362, '#skF_9'), '#skF_10')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9450, c_74])).
% 36.57/23.60  tff(c_9507, plain, (![B_3362]: (k3_xboole_0('#skF_9', B_3362)=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0(B_3362, '#skF_9'), '#skF_10')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_84, c_9471])).
% 36.57/23.60  tff(c_45018, plain, (![B_3906]: (k3_xboole_0('#skF_9', B_3906)='#skF_11' | k2_zfmisc_1(k3_xboole_0(B_3906, '#skF_9'), '#skF_10')!='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_44861, c_44861, c_9507])).
% 36.57/23.60  tff(c_45062, plain, (k3_xboole_0('#skF_9', '#skF_9')='#skF_11' | k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_52, c_45018])).
% 36.57/23.60  tff(c_45068, plain, ('#skF_11'='#skF_9' | k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_45062])).
% 36.57/23.60  tff(c_45069, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_99, c_45068])).
% 36.57/23.60  tff(c_46971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45370, c_45069])).
% 36.57/23.60  tff(c_46972, plain, (k4_xboole_0('#skF_12', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_44859])).
% 36.57/23.60  tff(c_47121, plain, (![D_19]: (r2_hidden(D_19, k1_xboole_0) | r2_hidden(D_19, '#skF_10') | ~r2_hidden(D_19, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_46972, c_28])).
% 36.57/23.60  tff(c_47188, plain, (![D_3917]: (r2_hidden(D_3917, '#skF_10') | ~r2_hidden(D_3917, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_221, c_47121])).
% 36.57/23.60  tff(c_55232, plain, (![A_3976]: (r1_tarski(A_3976, '#skF_10') | ~r2_hidden('#skF_1'(A_3976, '#skF_10'), '#skF_12'))), inference(resolution, [status(thm)], [c_47188, c_6])).
% 36.57/23.60  tff(c_55261, plain, (r1_tarski('#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_8, c_55232])).
% 36.57/23.60  tff(c_55268, plain, (k3_xboole_0('#skF_12', '#skF_10')='#skF_12'), inference(resolution, [status(thm)], [c_55261, c_58])).
% 36.57/23.60  tff(c_7864, plain, (![B_3280]: (k2_zfmisc_1(k3_xboole_0('#skF_9', B_3280), k3_xboole_0('#skF_10', '#skF_12'))=k2_zfmisc_1(k3_xboole_0('#skF_11', B_3280), '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_7809])).
% 36.57/23.60  tff(c_7873, plain, (![B_3280]: (k2_zfmisc_1(k3_xboole_0('#skF_9', B_3280), k3_xboole_0('#skF_12', '#skF_10'))=k2_zfmisc_1(k3_xboole_0('#skF_11', B_3280), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7864])).
% 36.57/23.60  tff(c_82035, plain, (![B_4316]: (k2_zfmisc_1(k3_xboole_0('#skF_11', B_4316), '#skF_12')=k2_zfmisc_1(k3_xboole_0('#skF_9', B_4316), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_55268, c_7873])).
% 36.57/23.60  tff(c_82269, plain, (![A_3893]: (k2_zfmisc_1(k3_xboole_0('#skF_9', k4_xboole_0(A_3893, '#skF_11')), '#skF_12')=k2_zfmisc_1(k1_xboole_0, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_42961, c_82035])).
% 36.57/23.60  tff(c_82366, plain, (![A_4317]: (k2_zfmisc_1(k3_xboole_0('#skF_9', k4_xboole_0(A_4317, '#skF_11')), '#skF_12')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_82269])).
% 36.57/23.60  tff(c_82558, plain, (k2_zfmisc_1(k4_xboole_0('#skF_9', '#skF_11'), '#skF_12')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11064, c_82366])).
% 36.57/23.60  tff(c_82760, plain, (k1_xboole_0='#skF_12' | k4_xboole_0('#skF_9', '#skF_11')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_82558, c_74])).
% 36.57/23.60  tff(c_82786, plain, (k4_xboole_0('#skF_9', '#skF_11')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52656, c_82760])).
% 36.57/23.60  tff(c_83013, plain, (![D_19]: (r2_hidden(D_19, k1_xboole_0) | r2_hidden(D_19, '#skF_11') | ~r2_hidden(D_19, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_82786, c_28])).
% 36.57/23.60  tff(c_84489, plain, (![D_4321]: (r2_hidden(D_4321, '#skF_11') | ~r2_hidden(D_4321, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_221, c_83013])).
% 36.57/23.60  tff(c_85921, plain, (![A_4329]: (r1_tarski(A_4329, '#skF_11') | ~r2_hidden('#skF_1'(A_4329, '#skF_11'), '#skF_9'))), inference(resolution, [status(thm)], [c_84489, c_6])).
% 36.57/23.60  tff(c_85949, plain, (r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_8, c_85921])).
% 36.57/23.60  tff(c_85959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58363, c_58363, c_85949])).
% 36.57/23.60  tff(c_85960, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_48265])).
% 36.57/23.60  tff(c_86018, plain, (![C_34]: (~r2_hidden(C_34, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_85960, c_221])).
% 36.57/23.60  tff(c_86022, plain, (![A_35]: (k2_zfmisc_1(A_35, '#skF_12')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_85960, c_85960, c_76])).
% 36.57/23.60  tff(c_87207, plain, (![A_3314]: (r2_hidden('#skF_5'(A_3314, A_3314, k2_zfmisc_1('#skF_9', '#skF_10')), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_86022, c_24004])).
% 36.57/23.60  tff(c_87242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86018, c_87207])).
% 36.57/23.60  tff(c_87243, plain, (k1_xboole_0='#skF_11' | k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_181])).
% 36.57/23.60  tff(c_87245, plain, (k1_xboole_0='#skF_12'), inference(splitLeft, [status(thm)], [c_87243])).
% 36.57/23.60  tff(c_86, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_104])).
% 36.57/23.60  tff(c_87272, plain, ('#skF_9'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_87245, c_86])).
% 36.57/23.60  tff(c_87271, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_87245, c_84])).
% 36.57/23.60  tff(c_87244, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_181])).
% 36.57/23.60  tff(c_87277, plain, (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_87245, c_87244])).
% 36.57/23.60  tff(c_87560, plain, (![B_4375, A_4376]: (B_4375='#skF_12' | A_4376='#skF_12' | k2_zfmisc_1(A_4376, B_4375)!='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_87245, c_87245, c_87245, c_74])).
% 36.57/23.60  tff(c_87569, plain, ('#skF_10'='#skF_12' | '#skF_9'='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_87277, c_87560])).
% 36.57/23.60  tff(c_87577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87272, c_87271, c_87569])).
% 36.57/23.60  tff(c_87578, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_87243])).
% 36.57/23.60  tff(c_87584, plain, ('#skF_11'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_87578, c_84])).
% 36.57/23.60  tff(c_87591, plain, (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_87578, c_87244])).
% 36.57/23.60  tff(c_87895, plain, (![B_4412, A_4413]: (B_4412='#skF_11' | A_4413='#skF_11' | k2_zfmisc_1(A_4413, B_4412)!='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_87578, c_87578, c_87578, c_74])).
% 36.57/23.60  tff(c_87904, plain, ('#skF_11'='#skF_10' | '#skF_11'='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_87591, c_87895])).
% 36.57/23.60  tff(c_87912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_87584, c_87904])).
% 36.57/23.60  tff(c_87913, plain, ('#skF_10'!='#skF_12'), inference(splitRight, [status(thm)], [c_82])).
% 36.57/23.60  tff(c_88045, plain, (![D_4436, B_4437, A_4438]: (~r2_hidden(D_4436, B_4437) | ~r2_hidden(D_4436, k4_xboole_0(A_4438, B_4437)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.57/23.60  tff(c_88049, plain, (![D_4439, A_4440]: (~r2_hidden(D_4439, A_4440) | ~r2_hidden(D_4439, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_88045])).
% 36.57/23.60  tff(c_88052, plain, (![C_34]: (~r2_hidden(C_34, k1_xboole_0))), inference(resolution, [status(thm)], [c_64, c_88049])).
% 36.57/23.60  tff(c_95959, plain, (![A_7675, B_7676, C_7677]: (r2_hidden('#skF_2'(A_7675, B_7676, C_7677), B_7676) | r2_hidden('#skF_3'(A_7675, B_7676, C_7677), C_7677) | k3_xboole_0(A_7675, B_7676)=C_7677)), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.57/23.60  tff(c_128755, plain, (![A_8244, B_8245, A_8246, B_8247]: (r2_hidden('#skF_3'(A_8244, B_8245, k4_xboole_0(A_8246, B_8247)), A_8246) | r2_hidden('#skF_2'(A_8244, B_8245, k4_xboole_0(A_8246, B_8247)), B_8245) | k4_xboole_0(A_8246, B_8247)=k3_xboole_0(A_8244, B_8245))), inference(resolution, [status(thm)], [c_95959, c_32])).
% 36.57/23.60  tff(c_128869, plain, (![A_8244, B_8245, A_29]: (r2_hidden('#skF_3'(A_8244, B_8245, k4_xboole_0(k1_xboole_0, A_29)), k1_xboole_0) | r2_hidden('#skF_2'(A_8244, B_8245, k1_xboole_0), B_8245) | k4_xboole_0(k1_xboole_0, A_29)=k3_xboole_0(A_8244, B_8245))), inference(superposition, [status(thm), theory('equality')], [c_60, c_128755])).
% 36.57/23.60  tff(c_128899, plain, (![A_8244, B_8245]: (r2_hidden('#skF_3'(A_8244, B_8245, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_2'(A_8244, B_8245, k1_xboole_0), B_8245) | k3_xboole_0(A_8244, B_8245)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_128869])).
% 36.57/23.60  tff(c_128900, plain, (![A_8244, B_8245]: (r2_hidden('#skF_2'(A_8244, B_8245, k1_xboole_0), B_8245) | k3_xboole_0(A_8244, B_8245)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_88052, c_128899])).
% 36.57/23.60  tff(c_95617, plain, (![A_7654, B_7655, C_7656]: (r2_hidden('#skF_2'(A_7654, B_7655, C_7656), A_7654) | r2_hidden('#skF_3'(A_7654, B_7655, C_7656), C_7656) | k3_xboole_0(A_7654, B_7655)=C_7656)), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.57/23.60  tff(c_135847, plain, (![A_8342, B_8343, B_8344, C_8345]: (~r2_hidden('#skF_2'(k4_xboole_0(A_8342, B_8343), B_8344, C_8345), B_8343) | r2_hidden('#skF_3'(k4_xboole_0(A_8342, B_8343), B_8344, C_8345), C_8345) | k3_xboole_0(k4_xboole_0(A_8342, B_8343), B_8344)=C_8345)), inference(resolution, [status(thm)], [c_95617, c_30])).
% 36.57/23.60  tff(c_135861, plain, (![A_8342, B_8245]: (r2_hidden('#skF_3'(k4_xboole_0(A_8342, B_8245), B_8245, k1_xboole_0), k1_xboole_0) | k3_xboole_0(k4_xboole_0(A_8342, B_8245), B_8245)=k1_xboole_0)), inference(resolution, [status(thm)], [c_128900, c_135847])).
% 36.57/23.60  tff(c_135914, plain, (![A_8342, B_8245]: (r2_hidden('#skF_3'(k4_xboole_0(A_8342, B_8245), B_8245, k1_xboole_0), k1_xboole_0) | k3_xboole_0(B_8245, k4_xboole_0(A_8342, B_8245))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_135861])).
% 36.57/23.60  tff(c_135936, plain, (![B_8346, A_8347]: (k3_xboole_0(B_8346, k4_xboole_0(A_8347, B_8346))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_88052, c_135914])).
% 36.57/23.60  tff(c_87914, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_82])).
% 36.57/23.60  tff(c_87919, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k2_zfmisc_1('#skF_9', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_87914, c_88])).
% 36.57/23.60  tff(c_88773, plain, (![A_4507, C_4508, B_4509, D_4510]: (k3_xboole_0(k2_zfmisc_1(A_4507, C_4508), k2_zfmisc_1(B_4509, D_4510))=k2_zfmisc_1(k3_xboole_0(A_4507, B_4509), k3_xboole_0(C_4508, D_4510)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 36.57/23.60  tff(c_88804, plain, (![A_4507, C_4508]: (k3_xboole_0(k2_zfmisc_1(A_4507, C_4508), k2_zfmisc_1('#skF_9', '#skF_12'))=k2_zfmisc_1(k3_xboole_0(A_4507, '#skF_9'), k3_xboole_0(C_4508, '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_87919, c_88773])).
% 36.57/23.60  tff(c_96107, plain, (![A_7682, C_7683]: (k2_zfmisc_1(k3_xboole_0(A_7682, '#skF_9'), k3_xboole_0(C_7683, '#skF_10'))=k2_zfmisc_1(k3_xboole_0(A_7682, '#skF_9'), k3_xboole_0(C_7683, '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_88804])).
% 36.57/23.60  tff(c_96150, plain, (![C_7683]: (k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_9'), k3_xboole_0(C_7683, '#skF_12'))=k2_zfmisc_1('#skF_9', k3_xboole_0(C_7683, '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_96107])).
% 36.57/23.60  tff(c_96163, plain, (![C_7684]: (k2_zfmisc_1('#skF_9', k3_xboole_0(C_7684, '#skF_10'))=k2_zfmisc_1('#skF_9', k3_xboole_0(C_7684, '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_96150])).
% 36.57/23.60  tff(c_96175, plain, (![C_7684]: (k3_xboole_0(C_7684, '#skF_10')=k1_xboole_0 | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_9', k3_xboole_0(C_7684, '#skF_12'))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96163, c_74])).
% 36.57/23.60  tff(c_96241, plain, (![C_7686]: (k3_xboole_0(C_7686, '#skF_10')=k1_xboole_0 | k2_zfmisc_1('#skF_9', k3_xboole_0(C_7686, '#skF_12'))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_86, c_96175])).
% 36.57/23.60  tff(c_96253, plain, (![B_2]: (k3_xboole_0(B_2, '#skF_10')=k1_xboole_0 | k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_12', B_2))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_96241])).
% 36.57/23.60  tff(c_136431, plain, (![A_8347]: (k3_xboole_0(k4_xboole_0(A_8347, '#skF_12'), '#skF_10')=k1_xboole_0 | k2_zfmisc_1('#skF_9', k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_135936, c_96253])).
% 36.57/23.60  tff(c_137452, plain, (![A_8350]: (k3_xboole_0('#skF_10', k4_xboole_0(A_8350, '#skF_12'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2, c_136431])).
% 36.57/23.60  tff(c_88061, plain, (![A_4449, B_4450]: (r2_hidden('#skF_1'(A_4449, B_4450), A_4449) | r1_tarski(A_4449, B_4450))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.57/23.60  tff(c_102027, plain, (![A_7847, B_7848, B_7849]: (r2_hidden('#skF_1'(k4_xboole_0(A_7847, B_7848), B_7849), A_7847) | r1_tarski(k4_xboole_0(A_7847, B_7848), B_7849))), inference(resolution, [status(thm)], [c_88061, c_32])).
% 36.57/23.60  tff(c_102082, plain, (![A_7850, B_7851]: (r1_tarski(k4_xboole_0(A_7850, B_7851), A_7850))), inference(resolution, [status(thm)], [c_102027, c_6])).
% 36.57/23.60  tff(c_102139, plain, (![A_7852, B_7853]: (k3_xboole_0(k4_xboole_0(A_7852, B_7853), A_7852)=k4_xboole_0(A_7852, B_7853))), inference(resolution, [status(thm)], [c_102082, c_58])).
% 36.57/23.60  tff(c_102311, plain, (![A_7852, B_7853]: (k3_xboole_0(A_7852, k4_xboole_0(A_7852, B_7853))=k4_xboole_0(A_7852, B_7853))), inference(superposition, [status(thm), theory('equality')], [c_102139, c_2])).
% 36.57/23.60  tff(c_137734, plain, (k4_xboole_0('#skF_10', '#skF_12')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_137452, c_102311])).
% 36.57/23.60  tff(c_138162, plain, (![D_19]: (r2_hidden(D_19, k1_xboole_0) | r2_hidden(D_19, '#skF_12') | ~r2_hidden(D_19, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_137734, c_28])).
% 36.57/23.60  tff(c_139037, plain, (![D_8357]: (r2_hidden(D_8357, '#skF_12') | ~r2_hidden(D_8357, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_88052, c_138162])).
% 36.57/23.60  tff(c_145578, plain, (![B_8429]: (r2_hidden('#skF_1'('#skF_10', B_8429), '#skF_12') | r1_tarski('#skF_10', B_8429))), inference(resolution, [status(thm)], [c_8, c_139037])).
% 36.57/23.60  tff(c_145599, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_145578, c_6])).
% 36.57/23.60  tff(c_88238, plain, (![C_4458, B_4459, A_4460]: (r2_hidden(C_4458, B_4459) | ~r2_hidden(C_4458, A_4460) | ~r1_tarski(A_4460, B_4459))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.57/23.60  tff(c_88401, plain, (![A_4479, B_4480, B_4481]: (r2_hidden('#skF_6'(A_4479, B_4480), B_4481) | ~r1_tarski(B_4480, B_4481) | ~r2_xboole_0(A_4479, B_4480))), inference(resolution, [status(thm)], [c_56, c_88238])).
% 36.57/23.60  tff(c_88451, plain, (![B_4484, B_4485]: (~r1_tarski(B_4484, B_4485) | ~r2_xboole_0(B_4485, B_4484))), inference(resolution, [status(thm)], [c_88401, c_54])).
% 36.57/23.60  tff(c_88455, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | B_21=A_20 | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_46, c_88451])).
% 36.57/23.60  tff(c_145604, plain, ('#skF_10'='#skF_12' | ~r1_tarski('#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_145599, c_88455])).
% 36.57/23.60  tff(c_145611, plain, (~r1_tarski('#skF_12', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_87913, c_145604])).
% 36.57/23.60  tff(c_88091, plain, (![A_4449]: (r1_tarski(A_4449, A_4449))), inference(resolution, [status(thm)], [c_88061, c_6])).
% 36.57/23.60  tff(c_88246, plain, (![A_3, B_4, B_4459]: (r2_hidden('#skF_1'(A_3, B_4), B_4459) | ~r1_tarski(A_3, B_4459) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_88238])).
% 36.57/23.60  tff(c_96260, plain, (![A_7687]: (k2_zfmisc_1('#skF_9', k3_xboole_0(A_7687, '#skF_12'))=k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_10', A_7687)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_96163])).
% 36.57/23.60  tff(c_96321, plain, (![B_2]: (k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_10', B_2))=k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_12', B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_96260])).
% 36.57/23.60  tff(c_136423, plain, (![A_8347]: (k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_12', k4_xboole_0(A_8347, '#skF_10')))=k2_zfmisc_1('#skF_9', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_135936, c_96321])).
% 36.57/23.60  tff(c_140520, plain, (![A_8374]: (k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_12', k4_xboole_0(A_8374, '#skF_10')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_136423])).
% 36.57/23.60  tff(c_96295, plain, (![A_7687]: (k3_xboole_0(A_7687, '#skF_12')=k1_xboole_0 | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_10', A_7687))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96260, c_74])).
% 36.57/23.60  tff(c_96336, plain, (![A_7687]: (k3_xboole_0(A_7687, '#skF_12')=k1_xboole_0 | k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_10', A_7687))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_86, c_96295])).
% 36.57/23.60  tff(c_96779, plain, (![A_7687]: (k3_xboole_0(A_7687, '#skF_12')=k1_xboole_0 | k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_12', A_7687))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_96321, c_96336])).
% 36.57/23.60  tff(c_140817, plain, (![A_8379]: (k3_xboole_0(k4_xboole_0(A_8379, '#skF_10'), '#skF_12')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_140520, c_96779])).
% 36.57/23.60  tff(c_102136, plain, (![A_7850, B_7851]: (k3_xboole_0(k4_xboole_0(A_7850, B_7851), A_7850)=k4_xboole_0(A_7850, B_7851))), inference(resolution, [status(thm)], [c_102082, c_58])).
% 36.57/23.60  tff(c_141124, plain, (k4_xboole_0('#skF_12', '#skF_10')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_140817, c_102136])).
% 36.57/23.60  tff(c_141576, plain, (![D_19]: (r2_hidden(D_19, k1_xboole_0) | r2_hidden(D_19, '#skF_10') | ~r2_hidden(D_19, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_141124, c_28])).
% 36.57/23.60  tff(c_141649, plain, (![D_19]: (r2_hidden(D_19, '#skF_10') | ~r2_hidden(D_19, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_88052, c_141576])).
% 36.57/23.60  tff(c_100012, plain, (![A_7822, B_7823, B_7824]: (r2_hidden('#skF_1'(k3_xboole_0(A_7822, B_7823), B_7824), B_7823) | r1_tarski(k3_xboole_0(A_7822, B_7823), B_7824))), inference(resolution, [status(thm)], [c_88061, c_12])).
% 36.57/23.60  tff(c_100078, plain, (![A_7822, B_7823]: (r1_tarski(k3_xboole_0(A_7822, B_7823), B_7823))), inference(resolution, [status(thm)], [c_100012, c_6])).
% 36.57/23.60  tff(c_88245, plain, (![A_24, B_25, B_4459]: (r2_hidden('#skF_6'(A_24, B_25), B_4459) | ~r1_tarski(B_25, B_4459) | ~r2_xboole_0(A_24, B_25))), inference(resolution, [status(thm)], [c_56, c_88238])).
% 36.57/23.60  tff(c_88362, plain, (![D_4476, A_4477, B_4478]: (r2_hidden(D_4476, k3_xboole_0(A_4477, B_4478)) | ~r2_hidden(D_4476, B_4478) | ~r2_hidden(D_4476, A_4477))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.57/23.60  tff(c_119166, plain, (![A_8107, B_8108, B_8109]: (~r2_xboole_0(k3_xboole_0(A_8107, B_8108), B_8109) | ~r2_hidden('#skF_6'(k3_xboole_0(A_8107, B_8108), B_8109), B_8108) | ~r2_hidden('#skF_6'(k3_xboole_0(A_8107, B_8108), B_8109), A_8107))), inference(resolution, [status(thm)], [c_88362, c_54])).
% 36.57/23.60  tff(c_130163, plain, (![A_8264, B_8265]: (~r2_hidden('#skF_6'(k3_xboole_0(A_8264, B_8265), B_8265), A_8264) | ~r2_xboole_0(k3_xboole_0(A_8264, B_8265), B_8265))), inference(resolution, [status(thm)], [c_56, c_119166])).
% 36.57/23.60  tff(c_130340, plain, (![B_8266, B_8267]: (~r1_tarski(B_8266, B_8267) | ~r2_xboole_0(k3_xboole_0(B_8267, B_8266), B_8266))), inference(resolution, [status(thm)], [c_88245, c_130163])).
% 36.57/23.60  tff(c_130443, plain, (![B_21, B_8267]: (~r1_tarski(B_21, B_8267) | k3_xboole_0(B_8267, B_21)=B_21 | ~r1_tarski(k3_xboole_0(B_8267, B_21), B_21))), inference(resolution, [status(thm)], [c_46, c_130340])).
% 36.57/23.60  tff(c_130473, plain, (![B_21, B_8267]: (~r1_tarski(B_21, B_8267) | k3_xboole_0(B_8267, B_21)=B_21)), inference(demodulation, [status(thm), theory('equality')], [c_100078, c_130443])).
% 36.57/23.60  tff(c_145608, plain, (k3_xboole_0('#skF_12', '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_145599, c_130473])).
% 36.57/23.60  tff(c_145612, plain, (k3_xboole_0('#skF_10', '#skF_12')='#skF_10'), inference(resolution, [status(thm)], [c_145599, c_58])).
% 36.57/23.60  tff(c_123207, plain, (![A_8160, A_8161, B_8162]: (r1_tarski(A_8160, k3_xboole_0(A_8161, B_8162)) | ~r2_hidden('#skF_1'(A_8160, k3_xboole_0(A_8161, B_8162)), B_8162) | ~r2_hidden('#skF_1'(A_8160, k3_xboole_0(A_8161, B_8162)), A_8161))), inference(resolution, [status(thm)], [c_88362, c_6])).
% 36.57/23.60  tff(c_123327, plain, (![A_3, A_8161]: (~r2_hidden('#skF_1'(A_3, k3_xboole_0(A_8161, A_3)), A_8161) | r1_tarski(A_3, k3_xboole_0(A_8161, A_3)))), inference(resolution, [status(thm)], [c_8, c_123207])).
% 36.57/23.60  tff(c_146301, plain, (~r2_hidden('#skF_1'('#skF_12', '#skF_10'), '#skF_10') | r1_tarski('#skF_12', k3_xboole_0('#skF_10', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_145612, c_123327])).
% 36.57/23.60  tff(c_146714, plain, (~r2_hidden('#skF_1'('#skF_12', '#skF_10'), '#skF_10') | r1_tarski('#skF_12', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_145608, c_2, c_146301])).
% 36.57/23.60  tff(c_146715, plain, (~r2_hidden('#skF_1'('#skF_12', '#skF_10'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_145611, c_146714])).
% 36.57/23.60  tff(c_146830, plain, (~r2_hidden('#skF_1'('#skF_12', '#skF_10'), '#skF_12')), inference(resolution, [status(thm)], [c_141649, c_146715])).
% 36.57/23.60  tff(c_146836, plain, (~r1_tarski('#skF_12', '#skF_12') | r1_tarski('#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_88246, c_146830])).
% 36.57/23.60  tff(c_146842, plain, (r1_tarski('#skF_12', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_88091, c_146836])).
% 36.57/23.60  tff(c_146844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145611, c_146842])).
% 36.57/23.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.57/23.60  
% 36.57/23.60  Inference rules
% 36.57/23.60  ----------------------
% 36.57/23.60  #Ref     : 0
% 36.57/23.60  #Sup     : 34836
% 36.57/23.60  #Fact    : 4
% 36.57/23.60  #Define  : 0
% 36.57/23.60  #Split   : 12
% 36.57/23.60  #Chain   : 0
% 36.57/23.60  #Close   : 0
% 36.57/23.60  
% 36.57/23.60  Ordering : KBO
% 36.57/23.60  
% 36.57/23.60  Simplification rules
% 36.57/23.60  ----------------------
% 36.57/23.60  #Subsume      : 10143
% 36.57/23.60  #Demod        : 34494
% 36.57/23.60  #Tautology    : 8200
% 36.57/23.60  #SimpNegUnit  : 873
% 36.57/23.60  #BackRed      : 670
% 36.57/23.60  
% 36.57/23.60  #Partial instantiations: 3910
% 36.57/23.60  #Strategies tried      : 1
% 36.57/23.60  
% 36.57/23.60  Timing (in seconds)
% 36.57/23.60  ----------------------
% 36.57/23.60  Preprocessing        : 0.35
% 36.57/23.60  Parsing              : 0.17
% 36.57/23.60  CNF conversion       : 0.03
% 36.57/23.60  Main loop            : 22.42
% 36.57/23.60  Inferencing          : 3.13
% 36.57/23.60  Reduction            : 11.89
% 36.57/23.60  Demodulation         : 10.19
% 36.57/23.60  BG Simplification    : 0.39
% 36.57/23.60  Subsumption          : 5.70
% 36.57/23.60  Abstraction          : 0.63
% 36.57/23.60  MUC search           : 0.00
% 36.57/23.60  Cooper               : 0.00
% 36.57/23.60  Total                : 22.87
% 36.57/23.60  Index Insertion      : 0.00
% 36.57/23.60  Index Deletion       : 0.00
% 36.57/23.60  Index Matching       : 0.00
% 36.57/23.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
