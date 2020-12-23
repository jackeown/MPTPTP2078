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
% DateTime   : Thu Dec  3 09:54:14 EST 2020

% Result     : Theorem 52.06s
% Output     : CNFRefutation 52.40s
% Verified   : 
% Statistics : Number of formulae       :  246 (1430 expanded)
%              Number of leaves         :   41 ( 485 expanded)
%              Depth                    :   24
%              Number of atoms          :  377 (2719 expanded)
%              Number of equality atoms :  166 (1129 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_92,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_107,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_101,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_96,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_10'(A_47,B_48),B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_152,plain,(
    ! [B_67,A_68] : k3_xboole_0(B_67,A_68) = k3_xboole_0(A_68,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [A_34] : k3_xboole_0(A_34,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_168,plain,(
    ! [A_68] : k3_xboole_0(k1_xboole_0,A_68) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_70])).

tff(c_444,plain,(
    ! [D_102,B_103,A_104] :
      ( r2_hidden(D_102,B_103)
      | ~ r2_hidden(D_102,k3_xboole_0(A_104,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_475,plain,(
    ! [D_105,A_106] :
      ( r2_hidden(D_105,A_106)
      | ~ r2_hidden(D_105,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_444])).

tff(c_916,plain,(
    ! [A_1614,A_1615] :
      ( r2_hidden('#skF_10'(A_1614,k1_xboole_0),A_1615)
      | ~ r2_hidden(A_1614,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_96,c_475])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_953,plain,(
    ! [A_1615,A_1614] :
      ( ~ v1_xboole_0(A_1615)
      | ~ r2_hidden(A_1614,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_916,c_4])).

tff(c_954,plain,(
    ! [A_1614] : ~ r2_hidden(A_1614,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_953])).

tff(c_4144,plain,(
    ! [A_3666,B_3667,C_3668] :
      ( r2_hidden('#skF_3'(A_3666,B_3667,C_3668),A_3666)
      | r2_hidden('#skF_4'(A_3666,B_3667,C_3668),C_3668)
      | k3_xboole_0(A_3666,B_3667) = C_3668 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [D_17,A_12,B_13] :
      ( r2_hidden(D_17,A_12)
      | ~ r2_hidden(D_17,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_80004,plain,(
    ! [A_17026,B_17027,B_17028,C_17029] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_17026,B_17027),B_17028,C_17029),A_17026)
      | r2_hidden('#skF_4'(k3_xboole_0(A_17026,B_17027),B_17028,C_17029),C_17029)
      | k3_xboole_0(k3_xboole_0(A_17026,B_17027),B_17028) = C_17029 ) ),
    inference(resolution,[status(thm)],[c_4144,c_18])).

tff(c_80541,plain,(
    ! [A_68,B_17028,C_17029] :
      ( r2_hidden('#skF_3'(k3_xboole_0(k1_xboole_0,A_68),B_17028,C_17029),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_17028,C_17029),C_17029)
      | k3_xboole_0(k3_xboole_0(k1_xboole_0,A_68),B_17028) = C_17029 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_80004])).

tff(c_80668,plain,(
    ! [B_17028,C_17029] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_17028,C_17029),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_17028,C_17029),C_17029)
      | k1_xboole_0 = C_17029 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_168,c_168,c_80541])).

tff(c_80669,plain,(
    ! [B_17028,C_17029] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_17028,C_17029),C_17029)
      | k1_xboole_0 = C_17029 ) ),
    inference(negUnitSimplification,[status(thm)],[c_954,c_80668])).

tff(c_66,plain,(
    ! [B_31] : r1_tarski(B_31,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_98,plain,
    ( '#skF_14' != '#skF_12'
    | '#skF_11' != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_109,plain,(
    '#skF_11' != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_90,plain,(
    ! [B_42] : k2_zfmisc_1(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3510,plain,(
    ! [A_3372,B_3373,C_3374] :
      ( r2_hidden('#skF_3'(A_3372,B_3373,C_3374),B_3373)
      | r2_hidden('#skF_4'(A_3372,B_3373,C_3374),C_3374)
      | k3_xboole_0(A_3372,B_3373) = C_3374 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [D_17,B_13,A_12] :
      ( r2_hidden(D_17,B_13)
      | ~ r2_hidden(D_17,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_91388,plain,(
    ! [A_17658,B_17659,A_17660,B_17661] :
      ( r2_hidden('#skF_4'(A_17658,B_17659,k3_xboole_0(A_17660,B_17661)),B_17661)
      | r2_hidden('#skF_3'(A_17658,B_17659,k3_xboole_0(A_17660,B_17661)),B_17659)
      | k3_xboole_0(A_17660,B_17661) = k3_xboole_0(A_17658,B_17659) ) ),
    inference(resolution,[status(thm)],[c_3510,c_16])).

tff(c_91958,plain,(
    ! [A_17658,B_17659,A_34] :
      ( r2_hidden('#skF_4'(A_17658,B_17659,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_3'(A_17658,B_17659,k3_xboole_0(A_34,k1_xboole_0)),B_17659)
      | k3_xboole_0(A_34,k1_xboole_0) = k3_xboole_0(A_17658,B_17659) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_91388])).

tff(c_92070,plain,(
    ! [A_17658,B_17659] :
      ( r2_hidden('#skF_4'(A_17658,B_17659,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_3'(A_17658,B_17659,k1_xboole_0),B_17659)
      | k3_xboole_0(A_17658,B_17659) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_91958])).

tff(c_92071,plain,(
    ! [A_17658,B_17659] :
      ( r2_hidden('#skF_3'(A_17658,B_17659,k1_xboole_0),B_17659)
      | k3_xboole_0(A_17658,B_17659) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_954,c_92070])).

tff(c_34,plain,(
    ! [D_23,B_19,A_18] :
      ( ~ r2_hidden(D_23,B_19)
      | ~ r2_hidden(D_23,k4_xboole_0(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_112864,plain,(
    ! [A_18933,B_18934,B_18935,C_18936] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_18933,B_18934),B_18935,C_18936),B_18934)
      | r2_hidden('#skF_4'(k4_xboole_0(A_18933,B_18934),B_18935,C_18936),C_18936)
      | k3_xboole_0(k4_xboole_0(A_18933,B_18934),B_18935) = C_18936 ) ),
    inference(resolution,[status(thm)],[c_4144,c_34])).

tff(c_112879,plain,(
    ! [A_18933,B_17659] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_18933,B_17659),B_17659,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(k4_xboole_0(A_18933,B_17659),B_17659) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_92071,c_112864])).

tff(c_112965,plain,(
    ! [A_18933,B_17659] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_18933,B_17659),B_17659,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(B_17659,k4_xboole_0(A_18933,B_17659)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_112879])).

tff(c_112989,plain,(
    ! [B_18967,A_18968] : k3_xboole_0(B_18967,k4_xboole_0(A_18968,B_18967)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_954,c_112965])).

tff(c_267,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(A_74,B_75) = A_74
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_274,plain,(
    ! [B_31] : k3_xboole_0(B_31,B_31) = B_31 ),
    inference(resolution,[status(thm)],[c_66,c_267])).

tff(c_92,plain,(
    ! [A_43,C_45,B_44,D_46] : k3_xboole_0(k2_zfmisc_1(A_43,C_45),k2_zfmisc_1(B_44,D_46)) = k2_zfmisc_1(k3_xboole_0(A_43,B_44),k3_xboole_0(C_45,D_46)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_104,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k2_zfmisc_1('#skF_13','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2122,plain,(
    ! [A_2375,C_2376,B_2377,D_2378] : k3_xboole_0(k2_zfmisc_1(A_2375,C_2376),k2_zfmisc_1(B_2377,D_2378)) = k2_zfmisc_1(k3_xboole_0(A_2375,B_2377),k3_xboole_0(C_2376,D_2378)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2175,plain,(
    ! [B_2377,D_2378] : k3_xboole_0(k2_zfmisc_1('#skF_13','#skF_14'),k2_zfmisc_1(B_2377,D_2378)) = k2_zfmisc_1(k3_xboole_0('#skF_11',B_2377),k3_xboole_0('#skF_12',D_2378)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_2122])).

tff(c_2567,plain,(
    ! [B_2729,D_2730] : k2_zfmisc_1(k3_xboole_0('#skF_11',B_2729),k3_xboole_0('#skF_12',D_2730)) = k2_zfmisc_1(k3_xboole_0('#skF_13',B_2729),k3_xboole_0('#skF_14',D_2730)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2175])).

tff(c_2593,plain,(
    ! [B_2729] : k2_zfmisc_1(k3_xboole_0('#skF_13',B_2729),k3_xboole_0('#skF_14','#skF_12')) = k2_zfmisc_1(k3_xboole_0('#skF_11',B_2729),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_2567])).

tff(c_2622,plain,(
    ! [B_2729] : k2_zfmisc_1(k3_xboole_0('#skF_13',B_2729),k3_xboole_0('#skF_12','#skF_14')) = k2_zfmisc_1(k3_xboole_0('#skF_11',B_2729),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2593])).

tff(c_113315,plain,(
    ! [A_18968] : k2_zfmisc_1(k3_xboole_0('#skF_11',k4_xboole_0(A_18968,'#skF_13')),'#skF_12') = k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_12','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_112989,c_2622])).

tff(c_126455,plain,(
    ! [A_19842] : k2_zfmisc_1(k3_xboole_0('#skF_11',k4_xboole_0(A_19842,'#skF_13')),'#skF_12') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_113315])).

tff(c_2178,plain,(
    ! [A_2375,C_2376] : k3_xboole_0(k2_zfmisc_1(A_2375,C_2376),k2_zfmisc_1('#skF_13','#skF_14')) = k2_zfmisc_1(k3_xboole_0(A_2375,'#skF_11'),k3_xboole_0(C_2376,'#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_2122])).

tff(c_2859,plain,(
    ! [A_2986,C_2987] : k2_zfmisc_1(k3_xboole_0(A_2986,'#skF_11'),k3_xboole_0(C_2987,'#skF_12')) = k2_zfmisc_1(k3_xboole_0(A_2986,'#skF_13'),k3_xboole_0(C_2987,'#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2178])).

tff(c_4491,plain,(
    ! [A_3765,C_3766] : k2_zfmisc_1(k3_xboole_0(A_3765,'#skF_13'),k3_xboole_0(C_3766,'#skF_14')) = k2_zfmisc_1(k3_xboole_0('#skF_11',A_3765),k3_xboole_0(C_3766,'#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2859])).

tff(c_2893,plain,(
    ! [A_2986] : k2_zfmisc_1(k3_xboole_0(A_2986,'#skF_13'),k3_xboole_0('#skF_12','#skF_14')) = k2_zfmisc_1(k3_xboole_0(A_2986,'#skF_11'),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_2859])).

tff(c_4501,plain,(
    ! [A_3765] : k2_zfmisc_1(k3_xboole_0('#skF_11',A_3765),k3_xboole_0('#skF_12','#skF_12')) = k2_zfmisc_1(k3_xboole_0(A_3765,'#skF_11'),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_4491,c_2893])).

tff(c_5970,plain,(
    ! [A_4283] : k2_zfmisc_1(k3_xboole_0(A_4283,'#skF_11'),'#skF_12') = k2_zfmisc_1(k3_xboole_0('#skF_11',A_4283),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_4501])).

tff(c_86,plain,(
    ! [B_42,A_41] :
      ( k1_xboole_0 = B_42
      | k1_xboole_0 = A_41
      | k2_zfmisc_1(A_41,B_42) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_5994,plain,(
    ! [A_4283] :
      ( k1_xboole_0 = '#skF_12'
      | k3_xboole_0(A_4283,'#skF_11') = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0('#skF_11',A_4283),'#skF_12') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5970,c_86])).

tff(c_6040,plain,(
    ! [A_4283] :
      ( k3_xboole_0(A_4283,'#skF_11') = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0('#skF_11',A_4283),'#skF_12') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_5994])).

tff(c_127125,plain,(
    ! [A_19907] : k3_xboole_0(k4_xboole_0(A_19907,'#skF_13'),'#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_126455,c_6040])).

tff(c_352,plain,(
    ! [D_89,A_90,B_91] :
      ( r2_hidden(D_89,A_90)
      | ~ r2_hidden(D_89,k4_xboole_0(A_90,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_25635,plain,(
    ! [A_9023,B_9024,B_9025] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_9023,B_9024),B_9025),A_9023)
      | r1_tarski(k4_xboole_0(A_9023,B_9024),B_9025) ) ),
    inference(resolution,[status(thm)],[c_12,c_352])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_25748,plain,(
    ! [A_9056,B_9057] : r1_tarski(k4_xboole_0(A_9056,B_9057),A_9056) ),
    inference(resolution,[status(thm)],[c_25635,c_10])).

tff(c_68,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_25880,plain,(
    ! [A_9056,B_9057] : k3_xboole_0(k4_xboole_0(A_9056,B_9057),A_9056) = k4_xboole_0(A_9056,B_9057) ),
    inference(resolution,[status(thm)],[c_25748,c_68])).

tff(c_127544,plain,(
    k4_xboole_0('#skF_11','#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_127125,c_25880])).

tff(c_32,plain,(
    ! [D_23,A_18,B_19] :
      ( r2_hidden(D_23,k4_xboole_0(A_18,B_19))
      | r2_hidden(D_23,B_19)
      | ~ r2_hidden(D_23,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_128332,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,k1_xboole_0)
      | r2_hidden(D_23,'#skF_13')
      | ~ r2_hidden(D_23,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127544,c_32])).

tff(c_130351,plain,(
    ! [D_20067] :
      ( r2_hidden(D_20067,'#skF_13')
      | ~ r2_hidden(D_20067,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_954,c_128332])).

tff(c_155232,plain,(
    ! [B_45566] :
      ( r2_hidden('#skF_2'('#skF_11',B_45566),'#skF_13')
      | r1_tarski('#skF_11',B_45566) ) ),
    inference(resolution,[status(thm)],[c_12,c_130351])).

tff(c_155266,plain,(
    r1_tarski('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_155232,c_10])).

tff(c_50,plain,(
    ! [A_24,B_25] :
      ( r2_xboole_0(A_24,B_25)
      | B_25 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_60,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_7'(A_27,B_28),B_28)
      | ~ r2_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_488,plain,(
    ! [A_106] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_106)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_475])).

tff(c_490,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_488])).

tff(c_25889,plain,(
    ! [A_9088,B_9089] : k3_xboole_0(k4_xboole_0(A_9088,B_9089),A_9088) = k4_xboole_0(A_9088,B_9089) ),
    inference(resolution,[status(thm)],[c_25748,c_68])).

tff(c_543,plain,(
    ! [D_115,A_116,B_117] :
      ( r2_hidden(D_115,A_116)
      | ~ r2_hidden(D_115,k3_xboole_0(A_116,B_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18778,plain,(
    ! [A_8312,B_8313,B_8314] :
      ( r2_hidden('#skF_2'(k3_xboole_0(A_8312,B_8313),B_8314),A_8312)
      | r1_tarski(k3_xboole_0(A_8312,B_8313),B_8314) ) ),
    inference(resolution,[status(thm)],[c_12,c_543])).

tff(c_18943,plain,(
    ! [A_8345,B_8346] : r1_tarski(k3_xboole_0(A_8345,B_8346),A_8345) ),
    inference(resolution,[status(thm)],[c_18778,c_10])).

tff(c_19126,plain,(
    ! [A_8345,B_8346] : k3_xboole_0(k3_xboole_0(A_8345,B_8346),A_8345) = k3_xboole_0(A_8345,B_8346) ),
    inference(resolution,[status(thm)],[c_18943,c_68])).

tff(c_25939,plain,(
    ! [A_9088,B_9089] : k3_xboole_0(k4_xboole_0(A_9088,B_9089),k4_xboole_0(A_9088,B_9089)) = k3_xboole_0(k4_xboole_0(A_9088,B_9089),A_9088) ),
    inference(superposition,[status(thm),theory(equality)],[c_25889,c_19126])).

tff(c_26329,plain,(
    ! [A_9088,B_9089] : k3_xboole_0(A_9088,k4_xboole_0(A_9088,B_9089)) = k4_xboole_0(A_9088,B_9089) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_2,c_25939])).

tff(c_19920,plain,(
    ! [A_8508,B_8509] : k3_xboole_0(k3_xboole_0(A_8508,B_8509),A_8508) = k3_xboole_0(A_8508,B_8509) ),
    inference(resolution,[status(thm)],[c_18943,c_68])).

tff(c_20395,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_19920])).

tff(c_113620,plain,(
    ! [A_18968,B_18967] : k3_xboole_0(k4_xboole_0(A_18968,B_18967),B_18967) = k3_xboole_0(k1_xboole_0,k4_xboole_0(A_18968,B_18967)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112989,c_20395])).

tff(c_114323,plain,(
    ! [A_18999,B_19000] : k3_xboole_0(k4_xboole_0(A_18999,B_19000),B_19000) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_113620])).

tff(c_5307,plain,(
    ! [A_3994,D_3995] : k2_zfmisc_1(k3_xboole_0(A_3994,'#skF_11'),k3_xboole_0('#skF_12',D_3995)) = k2_zfmisc_1(k3_xboole_0('#skF_13',A_3994),k3_xboole_0('#skF_14',D_3995)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2567])).

tff(c_5423,plain,(
    ! [A_3994] : k2_zfmisc_1(k3_xboole_0(A_3994,'#skF_11'),k3_xboole_0('#skF_12','#skF_14')) = k2_zfmisc_1(k3_xboole_0('#skF_13',A_3994),'#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_5307])).

tff(c_114587,plain,(
    ! [A_18999] : k2_zfmisc_1(k3_xboole_0('#skF_13',k4_xboole_0(A_18999,'#skF_11')),'#skF_14') = k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_12','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_114323,c_5423])).

tff(c_144187,plain,(
    ! [A_40662] : k2_zfmisc_1(k3_xboole_0('#skF_13',k4_xboole_0(A_40662,'#skF_11')),'#skF_14') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_114587])).

tff(c_144246,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_13','#skF_11'),'#skF_14') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26329,c_144187])).

tff(c_144341,plain,
    ( k1_xboole_0 = '#skF_14'
    | k4_xboole_0('#skF_13','#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_144246,c_86])).

tff(c_144344,plain,(
    k4_xboole_0('#skF_13','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_144341])).

tff(c_1237,plain,(
    ! [D_1870,A_1871,B_1872] :
      ( r2_hidden(D_1870,k4_xboole_0(A_1871,B_1872))
      | r2_hidden(D_1870,B_1872)
      | ~ r2_hidden(D_1870,A_1871) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1263,plain,(
    ! [A_1871,B_1872,D_1870] :
      ( ~ v1_xboole_0(k4_xboole_0(A_1871,B_1872))
      | r2_hidden(D_1870,B_1872)
      | ~ r2_hidden(D_1870,A_1871) ) ),
    inference(resolution,[status(thm)],[c_1237,c_4])).

tff(c_144640,plain,(
    ! [D_1870] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r2_hidden(D_1870,'#skF_11')
      | ~ r2_hidden(D_1870,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144344,c_1263])).

tff(c_144757,plain,(
    ! [D_40843] :
      ( r2_hidden(D_40843,'#skF_11')
      | ~ r2_hidden(D_40843,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_144640])).

tff(c_58,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden('#skF_7'(A_27,B_28),A_27)
      | ~ r2_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_165662,plain,(
    ! [B_48512] :
      ( ~ r2_xboole_0('#skF_11',B_48512)
      | ~ r2_hidden('#skF_7'('#skF_11',B_48512),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_144757,c_58])).

tff(c_165702,plain,(
    ~ r2_xboole_0('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_60,c_165662])).

tff(c_165705,plain,
    ( '#skF_11' = '#skF_13'
    | ~ r1_tarski('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_50,c_165702])).

tff(c_165708,plain,(
    '#skF_11' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155266,c_165705])).

tff(c_165710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_165708])).

tff(c_165711,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_144341])).

tff(c_88,plain,(
    ! [A_41] : k2_zfmisc_1(A_41,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2589,plain,(
    ! [D_2730] : k2_zfmisc_1(k3_xboole_0('#skF_13','#skF_11'),k3_xboole_0('#skF_14',D_2730)) = k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',D_2730)) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_2567])).

tff(c_113876,plain,(
    ! [A_18968] : k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',k4_xboole_0(A_18968,'#skF_14'))) = k2_zfmisc_1(k3_xboole_0('#skF_13','#skF_11'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_112989,c_2589])).

tff(c_122523,plain,(
    ! [A_19561] : k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',k4_xboole_0(A_19561,'#skF_14'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_113876])).

tff(c_102,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_16213,plain,(
    ! [D_7725,B_7726] :
      ( k3_xboole_0('#skF_12',D_7725) = k1_xboole_0
      | k3_xboole_0('#skF_11',B_7726) = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0('#skF_13',B_7726),k3_xboole_0('#skF_14',D_7725)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2567,c_86])).

tff(c_16299,plain,(
    ! [D_2730] :
      ( k3_xboole_0('#skF_12',D_2730) = k1_xboole_0
      | k3_xboole_0('#skF_11','#skF_11') = k1_xboole_0
      | k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',D_2730)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2589,c_16213])).

tff(c_16364,plain,(
    ! [D_2730] :
      ( k3_xboole_0('#skF_12',D_2730) = k1_xboole_0
      | k1_xboole_0 = '#skF_11'
      | k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',D_2730)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_16299])).

tff(c_16365,plain,(
    ! [D_2730] :
      ( k3_xboole_0('#skF_12',D_2730) = k1_xboole_0
      | k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',D_2730)) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_16364])).

tff(c_122646,plain,(
    ! [A_19592] : k3_xboole_0('#skF_12',k4_xboole_0(A_19592,'#skF_14')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_122523,c_16365])).

tff(c_123064,plain,(
    k4_xboole_0('#skF_12','#skF_14') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_122646,c_26329])).

tff(c_123825,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,k1_xboole_0)
      | r2_hidden(D_23,'#skF_14')
      | ~ r2_hidden(D_23,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123064,c_32])).

tff(c_124847,plain,(
    ! [D_19684] :
      ( r2_hidden(D_19684,'#skF_14')
      | ~ r2_hidden(D_19684,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_954,c_123825])).

tff(c_579,plain,(
    ! [C_118,B_119,A_120] :
      ( r2_hidden(C_118,B_119)
      | ~ r2_hidden(C_118,A_120)
      | ~ r1_tarski(A_120,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11180,plain,(
    ! [A_6291,B_6292,B_6293] :
      ( r2_hidden('#skF_10'(A_6291,B_6292),B_6293)
      | ~ r1_tarski(B_6292,B_6293)
      | ~ r2_hidden(A_6291,B_6292) ) ),
    inference(resolution,[status(thm)],[c_96,c_579])).

tff(c_11250,plain,(
    ! [B_6292,A_6291] :
      ( ~ r1_tarski(B_6292,k1_xboole_0)
      | ~ r2_hidden(A_6291,B_6292) ) ),
    inference(resolution,[status(thm)],[c_11180,c_954])).

tff(c_125053,plain,(
    ! [D_19684] :
      ( ~ r1_tarski('#skF_14',k1_xboole_0)
      | ~ r2_hidden(D_19684,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_124847,c_11250])).

tff(c_125920,plain,(
    ~ r1_tarski('#skF_14',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_125053])).

tff(c_166232,plain,(
    ~ r1_tarski('#skF_14','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165711,c_125920])).

tff(c_166406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_166232])).

tff(c_166410,plain,(
    ! [D_48697] : ~ r2_hidden(D_48697,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_125053])).

tff(c_166490,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_80669,c_166410])).

tff(c_166759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_166490])).

tff(c_166760,plain,(
    ! [A_1615] : ~ v1_xboole_0(A_1615) ),
    inference(splitRight,[status(thm)],[c_953])).

tff(c_166763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166760,c_490])).

tff(c_166764,plain,(
    ! [A_106] : r2_hidden('#skF_1'(k1_xboole_0),A_106) ),
    inference(splitRight,[status(thm)],[c_488])).

tff(c_166767,plain,(
    ! [A_48730] : r2_hidden('#skF_1'(k1_xboole_0),A_48730) ),
    inference(splitRight,[status(thm)],[c_488])).

tff(c_166778,plain,(
    ! [B_19] : ~ r2_hidden('#skF_1'(k1_xboole_0),B_19) ),
    inference(resolution,[status(thm)],[c_166767,c_34])).

tff(c_166797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166764,c_166778])).

tff(c_166798,plain,(
    '#skF_14' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_167035,plain,(
    ! [A_48758,B_48759] :
      ( r2_hidden('#skF_10'(A_48758,B_48759),B_48759)
      | ~ r2_hidden(A_48758,B_48759) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_167003,plain,(
    ! [D_48753,A_48754,B_48755] :
      ( r2_hidden(D_48753,A_48754)
      | ~ r2_hidden(D_48753,k3_xboole_0(A_48754,B_48755)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_167022,plain,(
    ! [D_48753,A_34] :
      ( r2_hidden(D_48753,A_34)
      | ~ r2_hidden(D_48753,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_167003])).

tff(c_167304,plain,(
    ! [A_48797,A_48798] :
      ( r2_hidden('#skF_10'(A_48797,k1_xboole_0),A_48798)
      | ~ r2_hidden(A_48797,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_167035,c_167022])).

tff(c_167340,plain,(
    ! [A_48798,A_48797] :
      ( ~ v1_xboole_0(A_48798)
      | ~ r2_hidden(A_48797,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_167304,c_4])).

tff(c_167341,plain,(
    ! [A_48797] : ~ r2_hidden(A_48797,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_167340])).

tff(c_170017,plain,(
    ! [A_51619,B_51620,C_51621] :
      ( r2_hidden('#skF_3'(A_51619,B_51620,C_51621),B_51620)
      | r2_hidden('#skF_4'(A_51619,B_51620,C_51621),C_51621)
      | k3_xboole_0(A_51619,B_51620) = C_51621 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_228130,plain,(
    ! [A_63264,B_63265,A_63266,B_63267] :
      ( r2_hidden('#skF_4'(A_63264,B_63265,k3_xboole_0(A_63266,B_63267)),B_63267)
      | r2_hidden('#skF_3'(A_63264,B_63265,k3_xboole_0(A_63266,B_63267)),B_63265)
      | k3_xboole_0(A_63266,B_63267) = k3_xboole_0(A_63264,B_63265) ) ),
    inference(resolution,[status(thm)],[c_170017,c_16])).

tff(c_228626,plain,(
    ! [A_63264,B_63265,A_34] :
      ( r2_hidden('#skF_4'(A_63264,B_63265,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_3'(A_63264,B_63265,k3_xboole_0(A_34,k1_xboole_0)),B_63265)
      | k3_xboole_0(A_63264,B_63265) = k3_xboole_0(A_34,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_228130])).

tff(c_228726,plain,(
    ! [A_63264,B_63265] :
      ( r2_hidden('#skF_4'(A_63264,B_63265,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_3'(A_63264,B_63265,k1_xboole_0),B_63265)
      | k3_xboole_0(A_63264,B_63265) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_228626])).

tff(c_228727,plain,(
    ! [A_63264,B_63265] :
      ( r2_hidden('#skF_3'(A_63264,B_63265,k1_xboole_0),B_63265)
      | k3_xboole_0(A_63264,B_63265) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_167341,c_228726])).

tff(c_169405,plain,(
    ! [A_51356,B_51357,C_51358] :
      ( r2_hidden('#skF_3'(A_51356,B_51357,C_51358),A_51356)
      | r2_hidden('#skF_4'(A_51356,B_51357,C_51358),C_51358)
      | k3_xboole_0(A_51356,B_51357) = C_51358 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_232059,plain,(
    ! [A_63886,B_63887,B_63888,C_63889] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_63886,B_63887),B_63888,C_63889),B_63887)
      | r2_hidden('#skF_4'(k4_xboole_0(A_63886,B_63887),B_63888,C_63889),C_63889)
      | k3_xboole_0(k4_xboole_0(A_63886,B_63887),B_63888) = C_63889 ) ),
    inference(resolution,[status(thm)],[c_169405,c_34])).

tff(c_232067,plain,(
    ! [A_63886,B_63265] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_63886,B_63265),B_63265,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(k4_xboole_0(A_63886,B_63265),B_63265) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_228727,c_232059])).

tff(c_232130,plain,(
    ! [A_63886,B_63265] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_63886,B_63265),B_63265,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(B_63265,k4_xboole_0(A_63886,B_63265)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_232067])).

tff(c_232154,plain,(
    ! [B_63920,A_63921] : k3_xboole_0(B_63920,k4_xboole_0(A_63921,B_63920)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_167341,c_232130])).

tff(c_166799,plain,(
    '#skF_11' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_166800,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166799,c_102])).

tff(c_166960,plain,(
    ! [A_48748,B_48749] :
      ( k3_xboole_0(A_48748,B_48749) = A_48748
      | ~ r1_tarski(A_48748,B_48749) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_166967,plain,(
    ! [B_31] : k3_xboole_0(B_31,B_31) = B_31 ),
    inference(resolution,[status(thm)],[c_66,c_166960])).

tff(c_166821,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') = k2_zfmisc_1('#skF_13','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166799,c_104])).

tff(c_168941,plain,(
    ! [A_51065,C_51066,B_51067,D_51068] : k3_xboole_0(k2_zfmisc_1(A_51065,C_51066),k2_zfmisc_1(B_51067,D_51068)) = k2_zfmisc_1(k3_xboole_0(A_51065,B_51067),k3_xboole_0(C_51066,D_51068)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_168988,plain,(
    ! [B_51067,D_51068] : k3_xboole_0(k2_zfmisc_1('#skF_13','#skF_12'),k2_zfmisc_1(B_51067,D_51068)) = k2_zfmisc_1(k3_xboole_0('#skF_13',B_51067),k3_xboole_0('#skF_14',D_51068)) ),
    inference(superposition,[status(thm),theory(equality)],[c_166821,c_168941])).

tff(c_170121,plain,(
    ! [B_51652,D_51653] : k2_zfmisc_1(k3_xboole_0('#skF_13',B_51652),k3_xboole_0('#skF_14',D_51653)) = k2_zfmisc_1(k3_xboole_0('#skF_13',B_51652),k3_xboole_0('#skF_12',D_51653)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_168988])).

tff(c_170159,plain,(
    ! [D_51653] : k2_zfmisc_1(k3_xboole_0('#skF_13','#skF_13'),k3_xboole_0('#skF_12',D_51653)) = k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_14',D_51653)) ),
    inference(superposition,[status(thm),theory(equality)],[c_166967,c_170121])).

tff(c_172955,plain,(
    ! [D_52972] : k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_14',D_52972)) = k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',D_52972)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166967,c_170159])).

tff(c_172971,plain,(
    ! [D_52972] :
      ( k3_xboole_0('#skF_14',D_52972) = k1_xboole_0
      | k1_xboole_0 = '#skF_13'
      | k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',D_52972)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172955,c_86])).

tff(c_173013,plain,(
    ! [D_52972] :
      ( k3_xboole_0('#skF_14',D_52972) = k1_xboole_0
      | k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',D_52972)) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_166800,c_172971])).

tff(c_232678,plain,(
    ! [A_63921] :
      ( k3_xboole_0('#skF_14',k4_xboole_0(A_63921,'#skF_12')) = k1_xboole_0
      | k2_zfmisc_1('#skF_13',k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232154,c_173013])).

tff(c_233069,plain,(
    ! [A_63952] : k3_xboole_0('#skF_14',k4_xboole_0(A_63952,'#skF_12')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_232678])).

tff(c_167081,plain,(
    ! [A_48765,B_48766] :
      ( r2_hidden('#skF_2'(A_48765,B_48766),A_48765)
      | r1_tarski(A_48765,B_48766) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36,plain,(
    ! [D_23,A_18,B_19] :
      ( r2_hidden(D_23,A_18)
      | ~ r2_hidden(D_23,k4_xboole_0(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_181782,plain,(
    ! [A_55789,B_55790,B_55791] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_55789,B_55790),B_55791),A_55789)
      | r1_tarski(k4_xboole_0(A_55789,B_55790),B_55791) ) ),
    inference(resolution,[status(thm)],[c_167081,c_36])).

tff(c_181880,plain,(
    ! [A_55822,B_55823] : r1_tarski(k4_xboole_0(A_55822,B_55823),A_55822) ),
    inference(resolution,[status(thm)],[c_181782,c_10])).

tff(c_182022,plain,(
    ! [A_55886,B_55887] : k3_xboole_0(k4_xboole_0(A_55886,B_55887),A_55886) = k4_xboole_0(A_55886,B_55887) ),
    inference(resolution,[status(thm)],[c_181880,c_68])).

tff(c_182331,plain,(
    ! [A_1,B_55887] : k3_xboole_0(A_1,k4_xboole_0(A_1,B_55887)) = k4_xboole_0(A_1,B_55887) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_182022])).

tff(c_233392,plain,(
    k4_xboole_0('#skF_14','#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_233069,c_182331])).

tff(c_233940,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,k1_xboole_0)
      | r2_hidden(D_23,'#skF_12')
      | ~ r2_hidden(D_23,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233392,c_32])).

tff(c_235663,plain,(
    ! [D_64076] :
      ( r2_hidden(D_64076,'#skF_12')
      | ~ r2_hidden(D_64076,'#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_167341,c_233940])).

tff(c_248479,plain,(
    ! [B_65927] :
      ( r2_hidden('#skF_2'('#skF_14',B_65927),'#skF_12')
      | r1_tarski('#skF_14',B_65927) ) ),
    inference(resolution,[status(thm)],[c_12,c_235663])).

tff(c_248510,plain,(
    r1_tarski('#skF_14','#skF_12') ),
    inference(resolution,[status(thm)],[c_248479,c_10])).

tff(c_62,plain,(
    ! [B_31,A_30] :
      ( B_31 = A_30
      | ~ r1_tarski(B_31,A_30)
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_248525,plain,
    ( '#skF_14' = '#skF_12'
    | ~ r1_tarski('#skF_12','#skF_14') ),
    inference(resolution,[status(thm)],[c_248510,c_62])).

tff(c_248538,plain,(
    ~ r1_tarski('#skF_12','#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_166798,c_248525])).

tff(c_170196,plain,(
    ! [D_51653] : k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_14',D_51653)) = k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',D_51653)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166967,c_170159])).

tff(c_232682,plain,(
    ! [A_63921] : k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',k4_xboole_0(A_63921,'#skF_14'))) = k2_zfmisc_1('#skF_13',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_232154,c_170196])).

tff(c_242280,plain,(
    ! [A_65292] : k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',k4_xboole_0(A_65292,'#skF_14'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_232682])).

tff(c_168991,plain,(
    ! [A_51065,C_51066] : k3_xboole_0(k2_zfmisc_1(A_51065,C_51066),k2_zfmisc_1('#skF_13','#skF_12')) = k2_zfmisc_1(k3_xboole_0(A_51065,'#skF_13'),k3_xboole_0(C_51066,'#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_166821,c_168941])).

tff(c_170303,plain,(
    ! [A_51717,C_51718] : k2_zfmisc_1(k3_xboole_0(A_51717,'#skF_13'),k3_xboole_0(C_51718,'#skF_14')) = k2_zfmisc_1(k3_xboole_0(A_51717,'#skF_13'),k3_xboole_0(C_51718,'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_168991])).

tff(c_170349,plain,(
    ! [C_51718] : k2_zfmisc_1(k3_xboole_0('#skF_13','#skF_13'),k3_xboole_0(C_51718,'#skF_12')) = k2_zfmisc_1('#skF_13',k3_xboole_0(C_51718,'#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_166967,c_170303])).

tff(c_172697,plain,(
    ! [C_52877] : k2_zfmisc_1('#skF_13',k3_xboole_0(C_52877,'#skF_14')) = k2_zfmisc_1('#skF_13',k3_xboole_0(C_52877,'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166967,c_170349])).

tff(c_173381,plain,(
    ! [A_53191] : k2_zfmisc_1('#skF_13',k3_xboole_0(A_53191,'#skF_12')) = k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_14',A_53191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_172697])).

tff(c_173419,plain,(
    ! [A_53191] :
      ( k3_xboole_0(A_53191,'#skF_12') = k1_xboole_0
      | k1_xboole_0 = '#skF_13'
      | k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_14',A_53191)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173381,c_86])).

tff(c_173481,plain,(
    ! [A_53191] :
      ( k3_xboole_0(A_53191,'#skF_12') = k1_xboole_0
      | k1_xboole_0 = '#skF_13'
      | k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',A_53191)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170196,c_173419])).

tff(c_173482,plain,(
    ! [A_53191] :
      ( k3_xboole_0(A_53191,'#skF_12') = k1_xboole_0
      | k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',A_53191)) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_166800,c_173481])).

tff(c_242381,plain,(
    ! [A_65323] : k3_xboole_0(k4_xboole_0(A_65323,'#skF_14'),'#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_242280,c_173482])).

tff(c_181978,plain,(
    ! [A_55822,B_55823] : k3_xboole_0(k4_xboole_0(A_55822,B_55823),A_55822) = k4_xboole_0(A_55822,B_55823) ),
    inference(resolution,[status(thm)],[c_181880,c_68])).

tff(c_242725,plain,(
    k4_xboole_0('#skF_12','#skF_14') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_242381,c_181978])).

tff(c_243310,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,k1_xboole_0)
      | r2_hidden(D_23,'#skF_14')
      | ~ r2_hidden(D_23,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242725,c_32])).

tff(c_245463,plain,(
    ! [D_65483] :
      ( r2_hidden(D_65483,'#skF_14')
      | ~ r2_hidden(D_65483,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_167341,c_243310])).

tff(c_253846,plain,(
    ! [A_66833] :
      ( r1_tarski(A_66833,'#skF_14')
      | ~ r2_hidden('#skF_2'(A_66833,'#skF_14'),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_245463,c_10])).

tff(c_253886,plain,(
    r1_tarski('#skF_12','#skF_14') ),
    inference(resolution,[status(thm)],[c_12,c_253846])).

tff(c_253898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248538,c_248538,c_253886])).

tff(c_253899,plain,(
    ! [A_48798] : ~ v1_xboole_0(A_48798) ),
    inference(splitRight,[status(thm)],[c_167340])).

tff(c_167024,plain,(
    ! [D_48756,A_48757] :
      ( r2_hidden(D_48756,A_48757)
      | ~ r2_hidden(D_48756,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_167003])).

tff(c_167028,plain,(
    ! [A_48757] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_48757)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_167024])).

tff(c_167029,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_167028])).

tff(c_253928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_253899,c_167029])).

tff(c_253931,plain,(
    ! [A_66867] : r2_hidden('#skF_1'(k1_xboole_0),A_66867) ),
    inference(splitRight,[status(thm)],[c_167028])).

tff(c_74,plain,(
    ! [C_40,A_36] :
      ( C_40 = A_36
      | ~ r2_hidden(C_40,k1_tarski(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_254102,plain,(
    '#skF_1'(k1_xboole_0) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_253931,c_74])).

tff(c_253973,plain,(
    ! [A_66871] : A_66871 = '#skF_1'(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_253931,c_74])).

tff(c_254320,plain,(
    ! [A_69364] : A_69364 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_254102,c_253973])).

tff(c_254373,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_254320,c_166798])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 52.06/39.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.24/39.14  
% 52.24/39.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.24/39.14  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_9 > #skF_12
% 52.24/39.14  
% 52.24/39.14  %Foreground sorts:
% 52.24/39.14  
% 52.24/39.14  
% 52.24/39.14  %Background operators:
% 52.24/39.14  
% 52.24/39.14  
% 52.24/39.14  %Foreground operators:
% 52.24/39.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 52.24/39.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 52.24/39.14  tff('#skF_11', type, '#skF_11': $i).
% 52.24/39.14  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 52.24/39.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 52.24/39.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 52.24/39.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 52.24/39.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 52.24/39.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 52.24/39.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 52.24/39.14  tff('#skF_14', type, '#skF_14': $i).
% 52.24/39.14  tff('#skF_13', type, '#skF_13': $i).
% 52.24/39.14  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 52.24/39.14  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 52.24/39.14  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 52.24/39.14  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 52.24/39.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 52.24/39.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 52.24/39.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 52.24/39.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 52.24/39.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 52.24/39.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 52.24/39.14  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 52.24/39.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 52.24/39.14  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 52.24/39.14  tff('#skF_12', type, '#skF_12': $i).
% 52.24/39.14  
% 52.40/39.18  tff(f_133, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 52.40/39.18  tff(f_122, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 52.40/39.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 52.40/39.18  tff(f_92, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 52.40/39.18  tff(f_49, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 52.40/39.18  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 52.40/39.18  tff(f_86, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 52.40/39.18  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 52.40/39.18  tff(f_107, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 52.40/39.18  tff(f_59, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 52.40/39.18  tff(f_90, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 52.40/39.18  tff(f_109, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 52.40/39.18  tff(f_66, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 52.40/39.18  tff(f_80, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 52.40/39.18  tff(f_101, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 52.40/39.18  tff(c_100, plain, (k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_133])).
% 52.40/39.18  tff(c_96, plain, (![A_47, B_48]: (r2_hidden('#skF_10'(A_47, B_48), B_48) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_122])).
% 52.40/39.18  tff(c_152, plain, (![B_67, A_68]: (k3_xboole_0(B_67, A_68)=k3_xboole_0(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_27])).
% 52.40/39.18  tff(c_70, plain, (![A_34]: (k3_xboole_0(A_34, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_92])).
% 52.40/39.18  tff(c_168, plain, (![A_68]: (k3_xboole_0(k1_xboole_0, A_68)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_70])).
% 52.40/39.18  tff(c_444, plain, (![D_102, B_103, A_104]: (r2_hidden(D_102, B_103) | ~r2_hidden(D_102, k3_xboole_0(A_104, B_103)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 52.40/39.18  tff(c_475, plain, (![D_105, A_106]: (r2_hidden(D_105, A_106) | ~r2_hidden(D_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_168, c_444])).
% 52.40/39.18  tff(c_916, plain, (![A_1614, A_1615]: (r2_hidden('#skF_10'(A_1614, k1_xboole_0), A_1615) | ~r2_hidden(A_1614, k1_xboole_0))), inference(resolution, [status(thm)], [c_96, c_475])).
% 52.40/39.18  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 52.40/39.18  tff(c_953, plain, (![A_1615, A_1614]: (~v1_xboole_0(A_1615) | ~r2_hidden(A_1614, k1_xboole_0))), inference(resolution, [status(thm)], [c_916, c_4])).
% 52.40/39.18  tff(c_954, plain, (![A_1614]: (~r2_hidden(A_1614, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_953])).
% 52.40/39.18  tff(c_4144, plain, (![A_3666, B_3667, C_3668]: (r2_hidden('#skF_3'(A_3666, B_3667, C_3668), A_3666) | r2_hidden('#skF_4'(A_3666, B_3667, C_3668), C_3668) | k3_xboole_0(A_3666, B_3667)=C_3668)), inference(cnfTransformation, [status(thm)], [f_49])).
% 52.40/39.18  tff(c_18, plain, (![D_17, A_12, B_13]: (r2_hidden(D_17, A_12) | ~r2_hidden(D_17, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 52.40/39.18  tff(c_80004, plain, (![A_17026, B_17027, B_17028, C_17029]: (r2_hidden('#skF_3'(k3_xboole_0(A_17026, B_17027), B_17028, C_17029), A_17026) | r2_hidden('#skF_4'(k3_xboole_0(A_17026, B_17027), B_17028, C_17029), C_17029) | k3_xboole_0(k3_xboole_0(A_17026, B_17027), B_17028)=C_17029)), inference(resolution, [status(thm)], [c_4144, c_18])).
% 52.40/39.18  tff(c_80541, plain, (![A_68, B_17028, C_17029]: (r2_hidden('#skF_3'(k3_xboole_0(k1_xboole_0, A_68), B_17028, C_17029), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_17028, C_17029), C_17029) | k3_xboole_0(k3_xboole_0(k1_xboole_0, A_68), B_17028)=C_17029)), inference(superposition, [status(thm), theory('equality')], [c_168, c_80004])).
% 52.40/39.18  tff(c_80668, plain, (![B_17028, C_17029]: (r2_hidden('#skF_3'(k1_xboole_0, B_17028, C_17029), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_17028, C_17029), C_17029) | k1_xboole_0=C_17029)), inference(demodulation, [status(thm), theory('equality')], [c_168, c_168, c_168, c_80541])).
% 52.40/39.18  tff(c_80669, plain, (![B_17028, C_17029]: (r2_hidden('#skF_4'(k1_xboole_0, B_17028, C_17029), C_17029) | k1_xboole_0=C_17029)), inference(negUnitSimplification, [status(thm)], [c_954, c_80668])).
% 52.40/39.18  tff(c_66, plain, (![B_31]: (r1_tarski(B_31, B_31))), inference(cnfTransformation, [status(thm)], [f_86])).
% 52.40/39.18  tff(c_98, plain, ('#skF_14'!='#skF_12' | '#skF_11'!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_133])).
% 52.40/39.18  tff(c_109, plain, ('#skF_11'!='#skF_13'), inference(splitLeft, [status(thm)], [c_98])).
% 52.40/39.18  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 52.40/39.18  tff(c_90, plain, (![B_42]: (k2_zfmisc_1(k1_xboole_0, B_42)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_107])).
% 52.40/39.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 52.40/39.18  tff(c_3510, plain, (![A_3372, B_3373, C_3374]: (r2_hidden('#skF_3'(A_3372, B_3373, C_3374), B_3373) | r2_hidden('#skF_4'(A_3372, B_3373, C_3374), C_3374) | k3_xboole_0(A_3372, B_3373)=C_3374)), inference(cnfTransformation, [status(thm)], [f_49])).
% 52.40/39.18  tff(c_16, plain, (![D_17, B_13, A_12]: (r2_hidden(D_17, B_13) | ~r2_hidden(D_17, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 52.40/39.18  tff(c_91388, plain, (![A_17658, B_17659, A_17660, B_17661]: (r2_hidden('#skF_4'(A_17658, B_17659, k3_xboole_0(A_17660, B_17661)), B_17661) | r2_hidden('#skF_3'(A_17658, B_17659, k3_xboole_0(A_17660, B_17661)), B_17659) | k3_xboole_0(A_17660, B_17661)=k3_xboole_0(A_17658, B_17659))), inference(resolution, [status(thm)], [c_3510, c_16])).
% 52.40/39.18  tff(c_91958, plain, (![A_17658, B_17659, A_34]: (r2_hidden('#skF_4'(A_17658, B_17659, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_3'(A_17658, B_17659, k3_xboole_0(A_34, k1_xboole_0)), B_17659) | k3_xboole_0(A_34, k1_xboole_0)=k3_xboole_0(A_17658, B_17659))), inference(superposition, [status(thm), theory('equality')], [c_70, c_91388])).
% 52.40/39.18  tff(c_92070, plain, (![A_17658, B_17659]: (r2_hidden('#skF_4'(A_17658, B_17659, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_3'(A_17658, B_17659, k1_xboole_0), B_17659) | k3_xboole_0(A_17658, B_17659)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_91958])).
% 52.40/39.18  tff(c_92071, plain, (![A_17658, B_17659]: (r2_hidden('#skF_3'(A_17658, B_17659, k1_xboole_0), B_17659) | k3_xboole_0(A_17658, B_17659)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_954, c_92070])).
% 52.40/39.18  tff(c_34, plain, (![D_23, B_19, A_18]: (~r2_hidden(D_23, B_19) | ~r2_hidden(D_23, k4_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 52.40/39.18  tff(c_112864, plain, (![A_18933, B_18934, B_18935, C_18936]: (~r2_hidden('#skF_3'(k4_xboole_0(A_18933, B_18934), B_18935, C_18936), B_18934) | r2_hidden('#skF_4'(k4_xboole_0(A_18933, B_18934), B_18935, C_18936), C_18936) | k3_xboole_0(k4_xboole_0(A_18933, B_18934), B_18935)=C_18936)), inference(resolution, [status(thm)], [c_4144, c_34])).
% 52.40/39.18  tff(c_112879, plain, (![A_18933, B_17659]: (r2_hidden('#skF_4'(k4_xboole_0(A_18933, B_17659), B_17659, k1_xboole_0), k1_xboole_0) | k3_xboole_0(k4_xboole_0(A_18933, B_17659), B_17659)=k1_xboole_0)), inference(resolution, [status(thm)], [c_92071, c_112864])).
% 52.40/39.18  tff(c_112965, plain, (![A_18933, B_17659]: (r2_hidden('#skF_4'(k4_xboole_0(A_18933, B_17659), B_17659, k1_xboole_0), k1_xboole_0) | k3_xboole_0(B_17659, k4_xboole_0(A_18933, B_17659))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_112879])).
% 52.40/39.18  tff(c_112989, plain, (![B_18967, A_18968]: (k3_xboole_0(B_18967, k4_xboole_0(A_18968, B_18967))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_954, c_112965])).
% 52.40/39.18  tff(c_267, plain, (![A_74, B_75]: (k3_xboole_0(A_74, B_75)=A_74 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_90])).
% 52.40/39.18  tff(c_274, plain, (![B_31]: (k3_xboole_0(B_31, B_31)=B_31)), inference(resolution, [status(thm)], [c_66, c_267])).
% 52.40/39.18  tff(c_92, plain, (![A_43, C_45, B_44, D_46]: (k3_xboole_0(k2_zfmisc_1(A_43, C_45), k2_zfmisc_1(B_44, D_46))=k2_zfmisc_1(k3_xboole_0(A_43, B_44), k3_xboole_0(C_45, D_46)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 52.40/39.18  tff(c_104, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k2_zfmisc_1('#skF_13', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_133])).
% 52.40/39.18  tff(c_2122, plain, (![A_2375, C_2376, B_2377, D_2378]: (k3_xboole_0(k2_zfmisc_1(A_2375, C_2376), k2_zfmisc_1(B_2377, D_2378))=k2_zfmisc_1(k3_xboole_0(A_2375, B_2377), k3_xboole_0(C_2376, D_2378)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 52.40/39.18  tff(c_2175, plain, (![B_2377, D_2378]: (k3_xboole_0(k2_zfmisc_1('#skF_13', '#skF_14'), k2_zfmisc_1(B_2377, D_2378))=k2_zfmisc_1(k3_xboole_0('#skF_11', B_2377), k3_xboole_0('#skF_12', D_2378)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_2122])).
% 52.40/39.18  tff(c_2567, plain, (![B_2729, D_2730]: (k2_zfmisc_1(k3_xboole_0('#skF_11', B_2729), k3_xboole_0('#skF_12', D_2730))=k2_zfmisc_1(k3_xboole_0('#skF_13', B_2729), k3_xboole_0('#skF_14', D_2730)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2175])).
% 52.40/39.18  tff(c_2593, plain, (![B_2729]: (k2_zfmisc_1(k3_xboole_0('#skF_13', B_2729), k3_xboole_0('#skF_14', '#skF_12'))=k2_zfmisc_1(k3_xboole_0('#skF_11', B_2729), '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_2567])).
% 52.40/39.18  tff(c_2622, plain, (![B_2729]: (k2_zfmisc_1(k3_xboole_0('#skF_13', B_2729), k3_xboole_0('#skF_12', '#skF_14'))=k2_zfmisc_1(k3_xboole_0('#skF_11', B_2729), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2593])).
% 52.40/39.18  tff(c_113315, plain, (![A_18968]: (k2_zfmisc_1(k3_xboole_0('#skF_11', k4_xboole_0(A_18968, '#skF_13')), '#skF_12')=k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_12', '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_112989, c_2622])).
% 52.40/39.18  tff(c_126455, plain, (![A_19842]: (k2_zfmisc_1(k3_xboole_0('#skF_11', k4_xboole_0(A_19842, '#skF_13')), '#skF_12')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_113315])).
% 52.40/39.18  tff(c_2178, plain, (![A_2375, C_2376]: (k3_xboole_0(k2_zfmisc_1(A_2375, C_2376), k2_zfmisc_1('#skF_13', '#skF_14'))=k2_zfmisc_1(k3_xboole_0(A_2375, '#skF_11'), k3_xboole_0(C_2376, '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_104, c_2122])).
% 52.40/39.18  tff(c_2859, plain, (![A_2986, C_2987]: (k2_zfmisc_1(k3_xboole_0(A_2986, '#skF_11'), k3_xboole_0(C_2987, '#skF_12'))=k2_zfmisc_1(k3_xboole_0(A_2986, '#skF_13'), k3_xboole_0(C_2987, '#skF_14')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2178])).
% 52.40/39.18  tff(c_4491, plain, (![A_3765, C_3766]: (k2_zfmisc_1(k3_xboole_0(A_3765, '#skF_13'), k3_xboole_0(C_3766, '#skF_14'))=k2_zfmisc_1(k3_xboole_0('#skF_11', A_3765), k3_xboole_0(C_3766, '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2859])).
% 52.40/39.18  tff(c_2893, plain, (![A_2986]: (k2_zfmisc_1(k3_xboole_0(A_2986, '#skF_13'), k3_xboole_0('#skF_12', '#skF_14'))=k2_zfmisc_1(k3_xboole_0(A_2986, '#skF_11'), '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_2859])).
% 52.40/39.18  tff(c_4501, plain, (![A_3765]: (k2_zfmisc_1(k3_xboole_0('#skF_11', A_3765), k3_xboole_0('#skF_12', '#skF_12'))=k2_zfmisc_1(k3_xboole_0(A_3765, '#skF_11'), '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_4491, c_2893])).
% 52.40/39.18  tff(c_5970, plain, (![A_4283]: (k2_zfmisc_1(k3_xboole_0(A_4283, '#skF_11'), '#skF_12')=k2_zfmisc_1(k3_xboole_0('#skF_11', A_4283), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_4501])).
% 52.40/39.18  tff(c_86, plain, (![B_42, A_41]: (k1_xboole_0=B_42 | k1_xboole_0=A_41 | k2_zfmisc_1(A_41, B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_107])).
% 52.40/39.18  tff(c_5994, plain, (![A_4283]: (k1_xboole_0='#skF_12' | k3_xboole_0(A_4283, '#skF_11')=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0('#skF_11', A_4283), '#skF_12')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5970, c_86])).
% 52.40/39.18  tff(c_6040, plain, (![A_4283]: (k3_xboole_0(A_4283, '#skF_11')=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0('#skF_11', A_4283), '#skF_12')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_100, c_5994])).
% 52.40/39.18  tff(c_127125, plain, (![A_19907]: (k3_xboole_0(k4_xboole_0(A_19907, '#skF_13'), '#skF_11')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_126455, c_6040])).
% 52.40/39.18  tff(c_352, plain, (![D_89, A_90, B_91]: (r2_hidden(D_89, A_90) | ~r2_hidden(D_89, k4_xboole_0(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 52.40/39.18  tff(c_25635, plain, (![A_9023, B_9024, B_9025]: (r2_hidden('#skF_2'(k4_xboole_0(A_9023, B_9024), B_9025), A_9023) | r1_tarski(k4_xboole_0(A_9023, B_9024), B_9025))), inference(resolution, [status(thm)], [c_12, c_352])).
% 52.40/39.18  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 52.40/39.18  tff(c_25748, plain, (![A_9056, B_9057]: (r1_tarski(k4_xboole_0(A_9056, B_9057), A_9056))), inference(resolution, [status(thm)], [c_25635, c_10])).
% 52.40/39.18  tff(c_68, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=A_32 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_90])).
% 52.40/39.18  tff(c_25880, plain, (![A_9056, B_9057]: (k3_xboole_0(k4_xboole_0(A_9056, B_9057), A_9056)=k4_xboole_0(A_9056, B_9057))), inference(resolution, [status(thm)], [c_25748, c_68])).
% 52.40/39.18  tff(c_127544, plain, (k4_xboole_0('#skF_11', '#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_127125, c_25880])).
% 52.40/39.18  tff(c_32, plain, (![D_23, A_18, B_19]: (r2_hidden(D_23, k4_xboole_0(A_18, B_19)) | r2_hidden(D_23, B_19) | ~r2_hidden(D_23, A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 52.40/39.18  tff(c_128332, plain, (![D_23]: (r2_hidden(D_23, k1_xboole_0) | r2_hidden(D_23, '#skF_13') | ~r2_hidden(D_23, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_127544, c_32])).
% 52.40/39.18  tff(c_130351, plain, (![D_20067]: (r2_hidden(D_20067, '#skF_13') | ~r2_hidden(D_20067, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_954, c_128332])).
% 52.40/39.18  tff(c_155232, plain, (![B_45566]: (r2_hidden('#skF_2'('#skF_11', B_45566), '#skF_13') | r1_tarski('#skF_11', B_45566))), inference(resolution, [status(thm)], [c_12, c_130351])).
% 52.40/39.18  tff(c_155266, plain, (r1_tarski('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_155232, c_10])).
% 52.40/39.18  tff(c_50, plain, (![A_24, B_25]: (r2_xboole_0(A_24, B_25) | B_25=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 52.40/39.18  tff(c_60, plain, (![A_27, B_28]: (r2_hidden('#skF_7'(A_27, B_28), B_28) | ~r2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 52.40/39.18  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 52.40/39.18  tff(c_488, plain, (![A_106]: (r2_hidden('#skF_1'(k1_xboole_0), A_106) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_475])).
% 52.40/39.18  tff(c_490, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_488])).
% 52.40/39.18  tff(c_25889, plain, (![A_9088, B_9089]: (k3_xboole_0(k4_xboole_0(A_9088, B_9089), A_9088)=k4_xboole_0(A_9088, B_9089))), inference(resolution, [status(thm)], [c_25748, c_68])).
% 52.40/39.18  tff(c_543, plain, (![D_115, A_116, B_117]: (r2_hidden(D_115, A_116) | ~r2_hidden(D_115, k3_xboole_0(A_116, B_117)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 52.40/39.18  tff(c_18778, plain, (![A_8312, B_8313, B_8314]: (r2_hidden('#skF_2'(k3_xboole_0(A_8312, B_8313), B_8314), A_8312) | r1_tarski(k3_xboole_0(A_8312, B_8313), B_8314))), inference(resolution, [status(thm)], [c_12, c_543])).
% 52.40/39.18  tff(c_18943, plain, (![A_8345, B_8346]: (r1_tarski(k3_xboole_0(A_8345, B_8346), A_8345))), inference(resolution, [status(thm)], [c_18778, c_10])).
% 52.40/39.18  tff(c_19126, plain, (![A_8345, B_8346]: (k3_xboole_0(k3_xboole_0(A_8345, B_8346), A_8345)=k3_xboole_0(A_8345, B_8346))), inference(resolution, [status(thm)], [c_18943, c_68])).
% 52.40/39.18  tff(c_25939, plain, (![A_9088, B_9089]: (k3_xboole_0(k4_xboole_0(A_9088, B_9089), k4_xboole_0(A_9088, B_9089))=k3_xboole_0(k4_xboole_0(A_9088, B_9089), A_9088))), inference(superposition, [status(thm), theory('equality')], [c_25889, c_19126])).
% 52.40/39.18  tff(c_26329, plain, (![A_9088, B_9089]: (k3_xboole_0(A_9088, k4_xboole_0(A_9088, B_9089))=k4_xboole_0(A_9088, B_9089))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_2, c_25939])).
% 52.40/39.18  tff(c_19920, plain, (![A_8508, B_8509]: (k3_xboole_0(k3_xboole_0(A_8508, B_8509), A_8508)=k3_xboole_0(A_8508, B_8509))), inference(resolution, [status(thm)], [c_18943, c_68])).
% 52.40/39.18  tff(c_20395, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_19920])).
% 52.40/39.18  tff(c_113620, plain, (![A_18968, B_18967]: (k3_xboole_0(k4_xboole_0(A_18968, B_18967), B_18967)=k3_xboole_0(k1_xboole_0, k4_xboole_0(A_18968, B_18967)))), inference(superposition, [status(thm), theory('equality')], [c_112989, c_20395])).
% 52.40/39.18  tff(c_114323, plain, (![A_18999, B_19000]: (k3_xboole_0(k4_xboole_0(A_18999, B_19000), B_19000)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_168, c_113620])).
% 52.40/39.18  tff(c_5307, plain, (![A_3994, D_3995]: (k2_zfmisc_1(k3_xboole_0(A_3994, '#skF_11'), k3_xboole_0('#skF_12', D_3995))=k2_zfmisc_1(k3_xboole_0('#skF_13', A_3994), k3_xboole_0('#skF_14', D_3995)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2567])).
% 52.40/39.18  tff(c_5423, plain, (![A_3994]: (k2_zfmisc_1(k3_xboole_0(A_3994, '#skF_11'), k3_xboole_0('#skF_12', '#skF_14'))=k2_zfmisc_1(k3_xboole_0('#skF_13', A_3994), '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_5307])).
% 52.40/39.18  tff(c_114587, plain, (![A_18999]: (k2_zfmisc_1(k3_xboole_0('#skF_13', k4_xboole_0(A_18999, '#skF_11')), '#skF_14')=k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_12', '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_114323, c_5423])).
% 52.40/39.18  tff(c_144187, plain, (![A_40662]: (k2_zfmisc_1(k3_xboole_0('#skF_13', k4_xboole_0(A_40662, '#skF_11')), '#skF_14')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_114587])).
% 52.40/39.18  tff(c_144246, plain, (k2_zfmisc_1(k4_xboole_0('#skF_13', '#skF_11'), '#skF_14')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26329, c_144187])).
% 52.40/39.18  tff(c_144341, plain, (k1_xboole_0='#skF_14' | k4_xboole_0('#skF_13', '#skF_11')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_144246, c_86])).
% 52.40/39.18  tff(c_144344, plain, (k4_xboole_0('#skF_13', '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_144341])).
% 52.40/39.18  tff(c_1237, plain, (![D_1870, A_1871, B_1872]: (r2_hidden(D_1870, k4_xboole_0(A_1871, B_1872)) | r2_hidden(D_1870, B_1872) | ~r2_hidden(D_1870, A_1871))), inference(cnfTransformation, [status(thm)], [f_59])).
% 52.40/39.18  tff(c_1263, plain, (![A_1871, B_1872, D_1870]: (~v1_xboole_0(k4_xboole_0(A_1871, B_1872)) | r2_hidden(D_1870, B_1872) | ~r2_hidden(D_1870, A_1871))), inference(resolution, [status(thm)], [c_1237, c_4])).
% 52.40/39.18  tff(c_144640, plain, (![D_1870]: (~v1_xboole_0(k1_xboole_0) | r2_hidden(D_1870, '#skF_11') | ~r2_hidden(D_1870, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_144344, c_1263])).
% 52.40/39.18  tff(c_144757, plain, (![D_40843]: (r2_hidden(D_40843, '#skF_11') | ~r2_hidden(D_40843, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_144640])).
% 52.40/39.18  tff(c_58, plain, (![A_27, B_28]: (~r2_hidden('#skF_7'(A_27, B_28), A_27) | ~r2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 52.40/39.18  tff(c_165662, plain, (![B_48512]: (~r2_xboole_0('#skF_11', B_48512) | ~r2_hidden('#skF_7'('#skF_11', B_48512), '#skF_13'))), inference(resolution, [status(thm)], [c_144757, c_58])).
% 52.40/39.18  tff(c_165702, plain, (~r2_xboole_0('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_60, c_165662])).
% 52.40/39.18  tff(c_165705, plain, ('#skF_11'='#skF_13' | ~r1_tarski('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_50, c_165702])).
% 52.40/39.18  tff(c_165708, plain, ('#skF_11'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_155266, c_165705])).
% 52.40/39.18  tff(c_165710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_165708])).
% 52.40/39.18  tff(c_165711, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_144341])).
% 52.40/39.18  tff(c_88, plain, (![A_41]: (k2_zfmisc_1(A_41, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_107])).
% 52.40/39.18  tff(c_2589, plain, (![D_2730]: (k2_zfmisc_1(k3_xboole_0('#skF_13', '#skF_11'), k3_xboole_0('#skF_14', D_2730))=k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', D_2730)))), inference(superposition, [status(thm), theory('equality')], [c_274, c_2567])).
% 52.40/39.18  tff(c_113876, plain, (![A_18968]: (k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', k4_xboole_0(A_18968, '#skF_14')))=k2_zfmisc_1(k3_xboole_0('#skF_13', '#skF_11'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_112989, c_2589])).
% 52.40/39.18  tff(c_122523, plain, (![A_19561]: (k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', k4_xboole_0(A_19561, '#skF_14')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_113876])).
% 52.40/39.18  tff(c_102, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_133])).
% 52.40/39.18  tff(c_16213, plain, (![D_7725, B_7726]: (k3_xboole_0('#skF_12', D_7725)=k1_xboole_0 | k3_xboole_0('#skF_11', B_7726)=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0('#skF_13', B_7726), k3_xboole_0('#skF_14', D_7725))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2567, c_86])).
% 52.40/39.18  tff(c_16299, plain, (![D_2730]: (k3_xboole_0('#skF_12', D_2730)=k1_xboole_0 | k3_xboole_0('#skF_11', '#skF_11')=k1_xboole_0 | k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', D_2730))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2589, c_16213])).
% 52.40/39.18  tff(c_16364, plain, (![D_2730]: (k3_xboole_0('#skF_12', D_2730)=k1_xboole_0 | k1_xboole_0='#skF_11' | k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', D_2730))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_274, c_16299])).
% 52.40/39.18  tff(c_16365, plain, (![D_2730]: (k3_xboole_0('#skF_12', D_2730)=k1_xboole_0 | k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', D_2730))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_102, c_16364])).
% 52.40/39.18  tff(c_122646, plain, (![A_19592]: (k3_xboole_0('#skF_12', k4_xboole_0(A_19592, '#skF_14'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_122523, c_16365])).
% 52.40/39.18  tff(c_123064, plain, (k4_xboole_0('#skF_12', '#skF_14')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_122646, c_26329])).
% 52.40/39.18  tff(c_123825, plain, (![D_23]: (r2_hidden(D_23, k1_xboole_0) | r2_hidden(D_23, '#skF_14') | ~r2_hidden(D_23, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_123064, c_32])).
% 52.40/39.18  tff(c_124847, plain, (![D_19684]: (r2_hidden(D_19684, '#skF_14') | ~r2_hidden(D_19684, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_954, c_123825])).
% 52.40/39.18  tff(c_579, plain, (![C_118, B_119, A_120]: (r2_hidden(C_118, B_119) | ~r2_hidden(C_118, A_120) | ~r1_tarski(A_120, B_119))), inference(cnfTransformation, [status(thm)], [f_40])).
% 52.40/39.18  tff(c_11180, plain, (![A_6291, B_6292, B_6293]: (r2_hidden('#skF_10'(A_6291, B_6292), B_6293) | ~r1_tarski(B_6292, B_6293) | ~r2_hidden(A_6291, B_6292))), inference(resolution, [status(thm)], [c_96, c_579])).
% 52.40/39.18  tff(c_11250, plain, (![B_6292, A_6291]: (~r1_tarski(B_6292, k1_xboole_0) | ~r2_hidden(A_6291, B_6292))), inference(resolution, [status(thm)], [c_11180, c_954])).
% 52.40/39.18  tff(c_125053, plain, (![D_19684]: (~r1_tarski('#skF_14', k1_xboole_0) | ~r2_hidden(D_19684, '#skF_12'))), inference(resolution, [status(thm)], [c_124847, c_11250])).
% 52.40/39.18  tff(c_125920, plain, (~r1_tarski('#skF_14', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_125053])).
% 52.40/39.18  tff(c_166232, plain, (~r1_tarski('#skF_14', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_165711, c_125920])).
% 52.40/39.18  tff(c_166406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_166232])).
% 52.40/39.18  tff(c_166410, plain, (![D_48697]: (~r2_hidden(D_48697, '#skF_12'))), inference(splitRight, [status(thm)], [c_125053])).
% 52.40/39.18  tff(c_166490, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_80669, c_166410])).
% 52.40/39.18  tff(c_166759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_166490])).
% 52.40/39.18  tff(c_166760, plain, (![A_1615]: (~v1_xboole_0(A_1615))), inference(splitRight, [status(thm)], [c_953])).
% 52.40/39.18  tff(c_166763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166760, c_490])).
% 52.40/39.18  tff(c_166764, plain, (![A_106]: (r2_hidden('#skF_1'(k1_xboole_0), A_106))), inference(splitRight, [status(thm)], [c_488])).
% 52.40/39.18  tff(c_166767, plain, (![A_48730]: (r2_hidden('#skF_1'(k1_xboole_0), A_48730))), inference(splitRight, [status(thm)], [c_488])).
% 52.40/39.18  tff(c_166778, plain, (![B_19]: (~r2_hidden('#skF_1'(k1_xboole_0), B_19))), inference(resolution, [status(thm)], [c_166767, c_34])).
% 52.40/39.18  tff(c_166797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166764, c_166778])).
% 52.40/39.18  tff(c_166798, plain, ('#skF_14'!='#skF_12'), inference(splitRight, [status(thm)], [c_98])).
% 52.40/39.18  tff(c_167035, plain, (![A_48758, B_48759]: (r2_hidden('#skF_10'(A_48758, B_48759), B_48759) | ~r2_hidden(A_48758, B_48759))), inference(cnfTransformation, [status(thm)], [f_122])).
% 52.40/39.18  tff(c_167003, plain, (![D_48753, A_48754, B_48755]: (r2_hidden(D_48753, A_48754) | ~r2_hidden(D_48753, k3_xboole_0(A_48754, B_48755)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 52.40/39.18  tff(c_167022, plain, (![D_48753, A_34]: (r2_hidden(D_48753, A_34) | ~r2_hidden(D_48753, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_70, c_167003])).
% 52.40/39.18  tff(c_167304, plain, (![A_48797, A_48798]: (r2_hidden('#skF_10'(A_48797, k1_xboole_0), A_48798) | ~r2_hidden(A_48797, k1_xboole_0))), inference(resolution, [status(thm)], [c_167035, c_167022])).
% 52.40/39.18  tff(c_167340, plain, (![A_48798, A_48797]: (~v1_xboole_0(A_48798) | ~r2_hidden(A_48797, k1_xboole_0))), inference(resolution, [status(thm)], [c_167304, c_4])).
% 52.40/39.18  tff(c_167341, plain, (![A_48797]: (~r2_hidden(A_48797, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_167340])).
% 52.40/39.18  tff(c_170017, plain, (![A_51619, B_51620, C_51621]: (r2_hidden('#skF_3'(A_51619, B_51620, C_51621), B_51620) | r2_hidden('#skF_4'(A_51619, B_51620, C_51621), C_51621) | k3_xboole_0(A_51619, B_51620)=C_51621)), inference(cnfTransformation, [status(thm)], [f_49])).
% 52.40/39.18  tff(c_228130, plain, (![A_63264, B_63265, A_63266, B_63267]: (r2_hidden('#skF_4'(A_63264, B_63265, k3_xboole_0(A_63266, B_63267)), B_63267) | r2_hidden('#skF_3'(A_63264, B_63265, k3_xboole_0(A_63266, B_63267)), B_63265) | k3_xboole_0(A_63266, B_63267)=k3_xboole_0(A_63264, B_63265))), inference(resolution, [status(thm)], [c_170017, c_16])).
% 52.40/39.18  tff(c_228626, plain, (![A_63264, B_63265, A_34]: (r2_hidden('#skF_4'(A_63264, B_63265, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_3'(A_63264, B_63265, k3_xboole_0(A_34, k1_xboole_0)), B_63265) | k3_xboole_0(A_63264, B_63265)=k3_xboole_0(A_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_70, c_228130])).
% 52.40/39.18  tff(c_228726, plain, (![A_63264, B_63265]: (r2_hidden('#skF_4'(A_63264, B_63265, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_3'(A_63264, B_63265, k1_xboole_0), B_63265) | k3_xboole_0(A_63264, B_63265)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_228626])).
% 52.40/39.18  tff(c_228727, plain, (![A_63264, B_63265]: (r2_hidden('#skF_3'(A_63264, B_63265, k1_xboole_0), B_63265) | k3_xboole_0(A_63264, B_63265)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_167341, c_228726])).
% 52.40/39.18  tff(c_169405, plain, (![A_51356, B_51357, C_51358]: (r2_hidden('#skF_3'(A_51356, B_51357, C_51358), A_51356) | r2_hidden('#skF_4'(A_51356, B_51357, C_51358), C_51358) | k3_xboole_0(A_51356, B_51357)=C_51358)), inference(cnfTransformation, [status(thm)], [f_49])).
% 52.40/39.18  tff(c_232059, plain, (![A_63886, B_63887, B_63888, C_63889]: (~r2_hidden('#skF_3'(k4_xboole_0(A_63886, B_63887), B_63888, C_63889), B_63887) | r2_hidden('#skF_4'(k4_xboole_0(A_63886, B_63887), B_63888, C_63889), C_63889) | k3_xboole_0(k4_xboole_0(A_63886, B_63887), B_63888)=C_63889)), inference(resolution, [status(thm)], [c_169405, c_34])).
% 52.40/39.18  tff(c_232067, plain, (![A_63886, B_63265]: (r2_hidden('#skF_4'(k4_xboole_0(A_63886, B_63265), B_63265, k1_xboole_0), k1_xboole_0) | k3_xboole_0(k4_xboole_0(A_63886, B_63265), B_63265)=k1_xboole_0)), inference(resolution, [status(thm)], [c_228727, c_232059])).
% 52.40/39.18  tff(c_232130, plain, (![A_63886, B_63265]: (r2_hidden('#skF_4'(k4_xboole_0(A_63886, B_63265), B_63265, k1_xboole_0), k1_xboole_0) | k3_xboole_0(B_63265, k4_xboole_0(A_63886, B_63265))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_232067])).
% 52.40/39.18  tff(c_232154, plain, (![B_63920, A_63921]: (k3_xboole_0(B_63920, k4_xboole_0(A_63921, B_63920))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_167341, c_232130])).
% 52.40/39.18  tff(c_166799, plain, ('#skF_11'='#skF_13'), inference(splitRight, [status(thm)], [c_98])).
% 52.40/39.18  tff(c_166800, plain, (k1_xboole_0!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_166799, c_102])).
% 52.40/39.18  tff(c_166960, plain, (![A_48748, B_48749]: (k3_xboole_0(A_48748, B_48749)=A_48748 | ~r1_tarski(A_48748, B_48749))), inference(cnfTransformation, [status(thm)], [f_90])).
% 52.40/39.18  tff(c_166967, plain, (![B_31]: (k3_xboole_0(B_31, B_31)=B_31)), inference(resolution, [status(thm)], [c_66, c_166960])).
% 52.40/39.18  tff(c_166821, plain, (k2_zfmisc_1('#skF_13', '#skF_14')=k2_zfmisc_1('#skF_13', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_166799, c_104])).
% 52.40/39.18  tff(c_168941, plain, (![A_51065, C_51066, B_51067, D_51068]: (k3_xboole_0(k2_zfmisc_1(A_51065, C_51066), k2_zfmisc_1(B_51067, D_51068))=k2_zfmisc_1(k3_xboole_0(A_51065, B_51067), k3_xboole_0(C_51066, D_51068)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 52.40/39.18  tff(c_168988, plain, (![B_51067, D_51068]: (k3_xboole_0(k2_zfmisc_1('#skF_13', '#skF_12'), k2_zfmisc_1(B_51067, D_51068))=k2_zfmisc_1(k3_xboole_0('#skF_13', B_51067), k3_xboole_0('#skF_14', D_51068)))), inference(superposition, [status(thm), theory('equality')], [c_166821, c_168941])).
% 52.40/39.18  tff(c_170121, plain, (![B_51652, D_51653]: (k2_zfmisc_1(k3_xboole_0('#skF_13', B_51652), k3_xboole_0('#skF_14', D_51653))=k2_zfmisc_1(k3_xboole_0('#skF_13', B_51652), k3_xboole_0('#skF_12', D_51653)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_168988])).
% 52.40/39.18  tff(c_170159, plain, (![D_51653]: (k2_zfmisc_1(k3_xboole_0('#skF_13', '#skF_13'), k3_xboole_0('#skF_12', D_51653))=k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_14', D_51653)))), inference(superposition, [status(thm), theory('equality')], [c_166967, c_170121])).
% 52.40/39.18  tff(c_172955, plain, (![D_52972]: (k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_14', D_52972))=k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', D_52972)))), inference(demodulation, [status(thm), theory('equality')], [c_166967, c_170159])).
% 52.40/39.18  tff(c_172971, plain, (![D_52972]: (k3_xboole_0('#skF_14', D_52972)=k1_xboole_0 | k1_xboole_0='#skF_13' | k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', D_52972))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_172955, c_86])).
% 52.40/39.18  tff(c_173013, plain, (![D_52972]: (k3_xboole_0('#skF_14', D_52972)=k1_xboole_0 | k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', D_52972))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_166800, c_172971])).
% 52.40/39.18  tff(c_232678, plain, (![A_63921]: (k3_xboole_0('#skF_14', k4_xboole_0(A_63921, '#skF_12'))=k1_xboole_0 | k2_zfmisc_1('#skF_13', k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_232154, c_173013])).
% 52.40/39.18  tff(c_233069, plain, (![A_63952]: (k3_xboole_0('#skF_14', k4_xboole_0(A_63952, '#skF_12'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_232678])).
% 52.40/39.18  tff(c_167081, plain, (![A_48765, B_48766]: (r2_hidden('#skF_2'(A_48765, B_48766), A_48765) | r1_tarski(A_48765, B_48766))), inference(cnfTransformation, [status(thm)], [f_40])).
% 52.40/39.18  tff(c_36, plain, (![D_23, A_18, B_19]: (r2_hidden(D_23, A_18) | ~r2_hidden(D_23, k4_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 52.40/39.18  tff(c_181782, plain, (![A_55789, B_55790, B_55791]: (r2_hidden('#skF_2'(k4_xboole_0(A_55789, B_55790), B_55791), A_55789) | r1_tarski(k4_xboole_0(A_55789, B_55790), B_55791))), inference(resolution, [status(thm)], [c_167081, c_36])).
% 52.40/39.18  tff(c_181880, plain, (![A_55822, B_55823]: (r1_tarski(k4_xboole_0(A_55822, B_55823), A_55822))), inference(resolution, [status(thm)], [c_181782, c_10])).
% 52.40/39.18  tff(c_182022, plain, (![A_55886, B_55887]: (k3_xboole_0(k4_xboole_0(A_55886, B_55887), A_55886)=k4_xboole_0(A_55886, B_55887))), inference(resolution, [status(thm)], [c_181880, c_68])).
% 52.40/39.18  tff(c_182331, plain, (![A_1, B_55887]: (k3_xboole_0(A_1, k4_xboole_0(A_1, B_55887))=k4_xboole_0(A_1, B_55887))), inference(superposition, [status(thm), theory('equality')], [c_2, c_182022])).
% 52.40/39.18  tff(c_233392, plain, (k4_xboole_0('#skF_14', '#skF_12')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_233069, c_182331])).
% 52.40/39.18  tff(c_233940, plain, (![D_23]: (r2_hidden(D_23, k1_xboole_0) | r2_hidden(D_23, '#skF_12') | ~r2_hidden(D_23, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_233392, c_32])).
% 52.40/39.18  tff(c_235663, plain, (![D_64076]: (r2_hidden(D_64076, '#skF_12') | ~r2_hidden(D_64076, '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_167341, c_233940])).
% 52.40/39.18  tff(c_248479, plain, (![B_65927]: (r2_hidden('#skF_2'('#skF_14', B_65927), '#skF_12') | r1_tarski('#skF_14', B_65927))), inference(resolution, [status(thm)], [c_12, c_235663])).
% 52.40/39.18  tff(c_248510, plain, (r1_tarski('#skF_14', '#skF_12')), inference(resolution, [status(thm)], [c_248479, c_10])).
% 52.40/39.18  tff(c_62, plain, (![B_31, A_30]: (B_31=A_30 | ~r1_tarski(B_31, A_30) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_86])).
% 52.40/39.18  tff(c_248525, plain, ('#skF_14'='#skF_12' | ~r1_tarski('#skF_12', '#skF_14')), inference(resolution, [status(thm)], [c_248510, c_62])).
% 52.40/39.18  tff(c_248538, plain, (~r1_tarski('#skF_12', '#skF_14')), inference(negUnitSimplification, [status(thm)], [c_166798, c_248525])).
% 52.40/39.18  tff(c_170196, plain, (![D_51653]: (k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_14', D_51653))=k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', D_51653)))), inference(demodulation, [status(thm), theory('equality')], [c_166967, c_170159])).
% 52.40/39.18  tff(c_232682, plain, (![A_63921]: (k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', k4_xboole_0(A_63921, '#skF_14')))=k2_zfmisc_1('#skF_13', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_232154, c_170196])).
% 52.40/39.18  tff(c_242280, plain, (![A_65292]: (k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', k4_xboole_0(A_65292, '#skF_14')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_232682])).
% 52.40/39.18  tff(c_168991, plain, (![A_51065, C_51066]: (k3_xboole_0(k2_zfmisc_1(A_51065, C_51066), k2_zfmisc_1('#skF_13', '#skF_12'))=k2_zfmisc_1(k3_xboole_0(A_51065, '#skF_13'), k3_xboole_0(C_51066, '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_166821, c_168941])).
% 52.40/39.18  tff(c_170303, plain, (![A_51717, C_51718]: (k2_zfmisc_1(k3_xboole_0(A_51717, '#skF_13'), k3_xboole_0(C_51718, '#skF_14'))=k2_zfmisc_1(k3_xboole_0(A_51717, '#skF_13'), k3_xboole_0(C_51718, '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_168991])).
% 52.40/39.18  tff(c_170349, plain, (![C_51718]: (k2_zfmisc_1(k3_xboole_0('#skF_13', '#skF_13'), k3_xboole_0(C_51718, '#skF_12'))=k2_zfmisc_1('#skF_13', k3_xboole_0(C_51718, '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_166967, c_170303])).
% 52.40/39.18  tff(c_172697, plain, (![C_52877]: (k2_zfmisc_1('#skF_13', k3_xboole_0(C_52877, '#skF_14'))=k2_zfmisc_1('#skF_13', k3_xboole_0(C_52877, '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_166967, c_170349])).
% 52.40/39.18  tff(c_173381, plain, (![A_53191]: (k2_zfmisc_1('#skF_13', k3_xboole_0(A_53191, '#skF_12'))=k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_14', A_53191)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_172697])).
% 52.40/39.18  tff(c_173419, plain, (![A_53191]: (k3_xboole_0(A_53191, '#skF_12')=k1_xboole_0 | k1_xboole_0='#skF_13' | k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_14', A_53191))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_173381, c_86])).
% 52.40/39.18  tff(c_173481, plain, (![A_53191]: (k3_xboole_0(A_53191, '#skF_12')=k1_xboole_0 | k1_xboole_0='#skF_13' | k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', A_53191))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_170196, c_173419])).
% 52.40/39.18  tff(c_173482, plain, (![A_53191]: (k3_xboole_0(A_53191, '#skF_12')=k1_xboole_0 | k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', A_53191))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_166800, c_173481])).
% 52.40/39.18  tff(c_242381, plain, (![A_65323]: (k3_xboole_0(k4_xboole_0(A_65323, '#skF_14'), '#skF_12')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_242280, c_173482])).
% 52.40/39.18  tff(c_181978, plain, (![A_55822, B_55823]: (k3_xboole_0(k4_xboole_0(A_55822, B_55823), A_55822)=k4_xboole_0(A_55822, B_55823))), inference(resolution, [status(thm)], [c_181880, c_68])).
% 52.40/39.18  tff(c_242725, plain, (k4_xboole_0('#skF_12', '#skF_14')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_242381, c_181978])).
% 52.40/39.18  tff(c_243310, plain, (![D_23]: (r2_hidden(D_23, k1_xboole_0) | r2_hidden(D_23, '#skF_14') | ~r2_hidden(D_23, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_242725, c_32])).
% 52.40/39.18  tff(c_245463, plain, (![D_65483]: (r2_hidden(D_65483, '#skF_14') | ~r2_hidden(D_65483, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_167341, c_243310])).
% 52.40/39.18  tff(c_253846, plain, (![A_66833]: (r1_tarski(A_66833, '#skF_14') | ~r2_hidden('#skF_2'(A_66833, '#skF_14'), '#skF_12'))), inference(resolution, [status(thm)], [c_245463, c_10])).
% 52.40/39.18  tff(c_253886, plain, (r1_tarski('#skF_12', '#skF_14')), inference(resolution, [status(thm)], [c_12, c_253846])).
% 52.40/39.18  tff(c_253898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248538, c_248538, c_253886])).
% 52.40/39.18  tff(c_253899, plain, (![A_48798]: (~v1_xboole_0(A_48798))), inference(splitRight, [status(thm)], [c_167340])).
% 52.40/39.18  tff(c_167024, plain, (![D_48756, A_48757]: (r2_hidden(D_48756, A_48757) | ~r2_hidden(D_48756, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_70, c_167003])).
% 52.40/39.18  tff(c_167028, plain, (![A_48757]: (r2_hidden('#skF_1'(k1_xboole_0), A_48757) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_167024])).
% 52.40/39.18  tff(c_167029, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_167028])).
% 52.40/39.18  tff(c_253928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_253899, c_167029])).
% 52.40/39.18  tff(c_253931, plain, (![A_66867]: (r2_hidden('#skF_1'(k1_xboole_0), A_66867))), inference(splitRight, [status(thm)], [c_167028])).
% 52.40/39.18  tff(c_74, plain, (![C_40, A_36]: (C_40=A_36 | ~r2_hidden(C_40, k1_tarski(A_36)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 52.40/39.18  tff(c_254102, plain, ('#skF_1'(k1_xboole_0)='#skF_12'), inference(resolution, [status(thm)], [c_253931, c_74])).
% 52.40/39.18  tff(c_253973, plain, (![A_66871]: (A_66871='#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_253931, c_74])).
% 52.40/39.18  tff(c_254320, plain, (![A_69364]: (A_69364='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_254102, c_253973])).
% 52.40/39.18  tff(c_254373, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_254320, c_166798])).
% 52.40/39.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.40/39.18  
% 52.40/39.18  Inference rules
% 52.40/39.18  ----------------------
% 52.40/39.18  #Ref     : 0
% 52.40/39.18  #Sup     : 62676
% 52.40/39.18  #Fact    : 14
% 52.40/39.18  #Define  : 0
% 52.40/39.18  #Split   : 39
% 52.40/39.18  #Chain   : 0
% 52.40/39.18  #Close   : 0
% 52.40/39.18  
% 52.40/39.18  Ordering : KBO
% 52.40/39.18  
% 52.40/39.18  Simplification rules
% 52.40/39.18  ----------------------
% 52.40/39.18  #Subsume      : 25564
% 52.40/39.18  #Demod        : 39913
% 52.40/39.18  #Tautology    : 11537
% 52.40/39.18  #SimpNegUnit  : 1455
% 52.40/39.18  #BackRed      : 920
% 52.40/39.18  
% 52.40/39.18  #Partial instantiations: 41016
% 52.40/39.18  #Strategies tried      : 1
% 52.40/39.18  
% 52.40/39.18  Timing (in seconds)
% 52.40/39.18  ----------------------
% 52.40/39.19  Preprocessing        : 0.36
% 52.40/39.19  Parsing              : 0.18
% 52.40/39.19  CNF conversion       : 0.03
% 52.40/39.19  Main loop            : 37.92
% 52.40/39.19  Inferencing          : 5.11
% 52.40/39.19  Reduction            : 14.94
% 52.40/39.19  Demodulation         : 12.03
% 52.40/39.19  BG Simplification    : 0.59
% 52.40/39.19  Subsumption          : 14.83
% 52.40/39.19  Abstraction          : 0.95
% 52.40/39.19  MUC search           : 0.00
% 52.40/39.19  Cooper               : 0.00
% 52.40/39.19  Total                : 38.38
% 52.40/39.19  Index Insertion      : 0.00
% 52.40/39.19  Index Deletion       : 0.00
% 52.40/39.19  Index Matching       : 0.00
% 52.40/39.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
