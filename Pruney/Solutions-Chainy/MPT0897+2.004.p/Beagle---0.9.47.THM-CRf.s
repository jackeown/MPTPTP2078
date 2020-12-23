%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:47 EST 2020

% Result     : Theorem 18.65s
% Output     : CNFRefutation 18.90s
% Verified   : 
% Statistics : Number of formulae       :  306 (3936 expanded)
%              Number of leaves         :   32 (1273 expanded)
%              Depth                    :   27
%              Number of atoms          :  468 (7623 expanded)
%              Number of equality atoms :  297 (5887 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_33,plain,(
    ! [A_24] :
      ( k1_xboole_0 = A_24
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_33])).

tff(c_30,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_30])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29254,plain,(
    ! [A_1031,B_1032,C_1033] :
      ( r2_hidden(k1_mcart_1(A_1031),B_1032)
      | ~ r2_hidden(A_1031,k2_zfmisc_1(B_1032,C_1033)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_29728,plain,(
    ! [B_1109,C_1110] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1109,C_1110))),B_1109)
      | v1_xboole_0(k2_zfmisc_1(B_1109,C_1110)) ) ),
    inference(resolution,[status(thm)],[c_4,c_29254])).

tff(c_29249,plain,(
    ! [A_1028,C_1029,B_1030] :
      ( r2_hidden(k2_mcart_1(A_1028),C_1029)
      | ~ r2_hidden(A_1028,k2_zfmisc_1(B_1030,C_1029)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_29337,plain,(
    ! [B_1049,C_1050] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1049,C_1050))),C_1050)
      | v1_xboole_0(k2_zfmisc_1(B_1049,C_1050)) ) ),
    inference(resolution,[status(thm)],[c_4,c_29249])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29368,plain,(
    ! [C_1057,B_1058] :
      ( ~ v1_xboole_0(C_1057)
      | v1_xboole_0(k2_zfmisc_1(B_1058,C_1057)) ) ),
    inference(resolution,[status(thm)],[c_29337,c_2])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_6])).

tff(c_29379,plain,(
    ! [B_1059,C_1060] :
      ( k2_zfmisc_1(B_1059,C_1060) = '#skF_2'
      | ~ v1_xboole_0(C_1060) ) ),
    inference(resolution,[status(thm)],[c_29368,c_38])).

tff(c_29386,plain,(
    ! [B_1061] : k2_zfmisc_1(B_1061,'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_29379])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden(k1_mcart_1(A_15),B_16)
      | ~ r2_hidden(A_15,k2_zfmisc_1(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_29560,plain,(
    ! [A_1087,B_1088] :
      ( r2_hidden(k1_mcart_1(A_1087),B_1088)
      | ~ r2_hidden(A_1087,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29386,c_20])).

tff(c_29576,plain,(
    ! [B_1088,A_1087] :
      ( ~ v1_xboole_0(B_1088)
      | ~ r2_hidden(A_1087,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_29560,c_2])).

tff(c_29577,plain,(
    ! [A_1087] : ~ r2_hidden(A_1087,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_29576])).

tff(c_29772,plain,(
    ! [C_1111] : v1_xboole_0(k2_zfmisc_1('#skF_2',C_1111)) ),
    inference(resolution,[status(thm)],[c_29728,c_29577])).

tff(c_29791,plain,(
    ! [C_1111] : k2_zfmisc_1('#skF_2',C_1111) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_29772,c_38])).

tff(c_29359,plain,(
    ! [C_1050,B_1049] :
      ( ~ v1_xboole_0(C_1050)
      | v1_xboole_0(k2_zfmisc_1(B_1049,C_1050)) ) ),
    inference(resolution,[status(thm)],[c_29337,c_2])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_29901,plain,(
    ! [B_1115,C_1116] :
      ( ~ v1_xboole_0(B_1115)
      | v1_xboole_0(k2_zfmisc_1(B_1115,C_1116)) ) ),
    inference(resolution,[status(thm)],[c_29728,c_2])).

tff(c_29925,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | v1_xboole_0(k3_zfmisc_1(A_8,B_9,C_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_29901])).

tff(c_21942,plain,(
    ! [A_683,C_684,B_685] :
      ( r2_hidden(k2_mcart_1(A_683),C_684)
      | ~ r2_hidden(A_683,k2_zfmisc_1(B_685,C_684)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22319,plain,(
    ! [B_762,C_763] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_762,C_763))),C_763)
      | v1_xboole_0(k2_zfmisc_1(B_762,C_763)) ) ),
    inference(resolution,[status(thm)],[c_4,c_21942])).

tff(c_21924,plain,(
    ! [A_678,B_679,C_680] :
      ( r2_hidden(k1_mcart_1(A_678),B_679)
      | ~ r2_hidden(A_678,k2_zfmisc_1(B_679,C_680)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22017,plain,(
    ! [B_699,C_700] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_699,C_700))),B_699)
      | v1_xboole_0(k2_zfmisc_1(B_699,C_700)) ) ),
    inference(resolution,[status(thm)],[c_4,c_21924])).

tff(c_22045,plain,(
    ! [B_701,C_702] :
      ( ~ v1_xboole_0(B_701)
      | v1_xboole_0(k2_zfmisc_1(B_701,C_702)) ) ),
    inference(resolution,[status(thm)],[c_22017,c_2])).

tff(c_22062,plain,(
    ! [B_709,C_710] :
      ( k2_zfmisc_1(B_709,C_710) = '#skF_2'
      | ~ v1_xboole_0(B_709) ) ),
    inference(resolution,[status(thm)],[c_22045,c_38])).

tff(c_22070,plain,(
    ! [C_711] : k2_zfmisc_1('#skF_2',C_711) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_22062])).

tff(c_22150,plain,(
    ! [A_726] :
      ( r2_hidden(k1_mcart_1(A_726),'#skF_2')
      | ~ r2_hidden(A_726,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22070,c_20])).

tff(c_22153,plain,(
    ! [A_726] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_726,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22150,c_2])).

tff(c_22156,plain,(
    ! [A_726] : ~ r2_hidden(A_726,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_22153])).

tff(c_22357,plain,(
    ! [B_764] : v1_xboole_0(k2_zfmisc_1(B_764,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_22319,c_22156])).

tff(c_22391,plain,(
    ! [B_765] : k2_zfmisc_1(B_765,'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22357,c_38])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_zfmisc_1(k3_zfmisc_1(A_11,B_12,C_13),D_14) = k4_zfmisc_1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22419,plain,(
    ! [A_11,B_12,C_13] : k4_zfmisc_1(A_11,B_12,C_13,'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_22391,c_16])).

tff(c_22069,plain,(
    ! [C_710] : k2_zfmisc_1('#skF_2',C_710) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_22062])).

tff(c_76,plain,(
    ! [A_32,C_33,B_34] :
      ( r2_hidden(k2_mcart_1(A_32),C_33)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_34,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_405,plain,(
    ! [B_99,C_100] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_99,C_100))),C_100)
      | v1_xboole_0(k2_zfmisc_1(B_99,C_100)) ) ),
    inference(resolution,[status(thm)],[c_4,c_76])).

tff(c_115,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden(k1_mcart_1(A_39),B_40)
      | ~ r2_hidden(A_39,k2_zfmisc_1(B_40,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_149,plain,(
    ! [B_50,C_51] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_50,C_51))),B_50)
      | v1_xboole_0(k2_zfmisc_1(B_50,C_51)) ) ),
    inference(resolution,[status(thm)],[c_4,c_115])).

tff(c_177,plain,(
    ! [B_52,C_53] :
      ( ~ v1_xboole_0(B_52)
      | v1_xboole_0(k2_zfmisc_1(B_52,C_53)) ) ),
    inference(resolution,[status(thm)],[c_149,c_2])).

tff(c_194,plain,(
    ! [B_60,C_61] :
      ( k2_zfmisc_1(B_60,C_61) = '#skF_2'
      | ~ v1_xboole_0(B_60) ) ),
    inference(resolution,[status(thm)],[c_177,c_38])).

tff(c_202,plain,(
    ! [C_62] : k2_zfmisc_1('#skF_2',C_62) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_194])).

tff(c_282,plain,(
    ! [A_77] :
      ( r2_hidden(k1_mcart_1(A_77),'#skF_2')
      | ~ r2_hidden(A_77,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_20])).

tff(c_285,plain,(
    ! [A_77] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_77,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_282,c_2])).

tff(c_288,plain,(
    ! [A_77] : ~ r2_hidden(A_77,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_285])).

tff(c_439,plain,(
    ! [B_101] : v1_xboole_0(k2_zfmisc_1(B_101,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_405,c_288])).

tff(c_470,plain,(
    ! [B_102] : k2_zfmisc_1(B_102,'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_439,c_38])).

tff(c_495,plain,(
    ! [A_11,B_12,C_13] : k4_zfmisc_1(A_11,B_12,C_13,'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_16])).

tff(c_28,plain,
    ( '#skF_10' != '#skF_6'
    | '#skF_5' != '#skF_9'
    | '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_61,plain,(
    ! [A_29,B_30,C_31] : k2_zfmisc_1(k2_zfmisc_1(A_29,B_30),C_31) = k3_zfmisc_1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    ! [A_29,B_30,C_31,C_10] : k3_zfmisc_1(k2_zfmisc_1(A_29,B_30),C_31,C_10) = k2_zfmisc_1(k3_zfmisc_1(A_29,B_30,C_31),C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_14])).

tff(c_958,plain,(
    ! [A_29,B_30,C_31,C_10] : k3_zfmisc_1(k2_zfmisc_1(A_29,B_30),C_31,C_10) = k4_zfmisc_1(A_29,B_30,C_31,C_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_64])).

tff(c_201,plain,(
    ! [C_61] : k2_zfmisc_1('#skF_2',C_61) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_194])).

tff(c_32,plain,(
    k4_zfmisc_1('#skF_7','#skF_8','#skF_9','#skF_10') = k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_122,plain,(
    ! [A_42,B_43,C_44,D_45] : k2_zfmisc_1(k3_zfmisc_1(A_42,B_43,C_44),D_45) = k4_zfmisc_1(A_42,B_43,C_44,D_45) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_relat_1(k2_zfmisc_1(A_6,B_7)) = B_7
      | k1_xboole_0 = B_7
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_99,plain,(
    ! [A_6,B_7] :
      ( k2_relat_1(k2_zfmisc_1(A_6,B_7)) = B_7
      | B_7 = '#skF_2'
      | A_6 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_37,c_10])).

tff(c_5121,plain,(
    ! [A_313,B_314,C_315,D_316] :
      ( k2_relat_1(k4_zfmisc_1(A_313,B_314,C_315,D_316)) = D_316
      | D_316 = '#skF_2'
      | k3_zfmisc_1(A_313,B_314,C_315) = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_99])).

tff(c_5163,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_10'
    | '#skF_10' = '#skF_2'
    | k3_zfmisc_1('#skF_7','#skF_8','#skF_9') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5121])).

tff(c_5171,plain,(
    k3_zfmisc_1('#skF_7','#skF_8','#skF_9') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5163])).

tff(c_1081,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_152,B_153,C_154))
      | v1_xboole_0(k4_zfmisc_1(A_152,B_153,C_154,D_155)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_177])).

tff(c_1109,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
    | v1_xboole_0(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1081])).

tff(c_1424,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1109])).

tff(c_5173,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5171,c_1424])).

tff(c_5177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5173])).

tff(c_5178,plain,
    ( '#skF_10' = '#skF_2'
    | k2_relat_1(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_5163])).

tff(c_5180,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_5178])).

tff(c_130,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k2_relat_1(k4_zfmisc_1(A_42,B_43,C_44,D_45)) = D_45
      | D_45 = '#skF_2'
      | k3_zfmisc_1(A_42,B_43,C_44) = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_99])).

tff(c_5184,plain,
    ( '#skF_10' = '#skF_6'
    | '#skF_6' = '#skF_2'
    | k3_zfmisc_1('#skF_3','#skF_4','#skF_5') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_5180,c_130])).

tff(c_5191,plain,(
    k3_zfmisc_1('#skF_3','#skF_4','#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5184])).

tff(c_5257,plain,(
    ! [D_14] : k4_zfmisc_1('#skF_3','#skF_4','#skF_5',D_14) = k2_zfmisc_1('#skF_2',D_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_5191,c_16])).

tff(c_5275,plain,(
    ! [D_14] : k4_zfmisc_1('#skF_3','#skF_4','#skF_5',D_14) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_5257])).

tff(c_5287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5275,c_50])).

tff(c_5288,plain,
    ( '#skF_6' = '#skF_2'
    | '#skF_10' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5184])).

tff(c_5290,plain,(
    '#skF_10' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_5288])).

tff(c_5306,plain,(
    k4_zfmisc_1('#skF_7','#skF_8','#skF_9','#skF_6') = k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5290,c_32])).

tff(c_960,plain,(
    ! [A_144,B_145,C_146,C_147] : k3_zfmisc_1(k2_zfmisc_1(A_144,B_145),C_146,C_147) = k4_zfmisc_1(A_144,B_145,C_146,C_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_64])).

tff(c_24,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] :
      ( E_22 = B_19
      | k3_zfmisc_1(A_18,B_19,C_20) = k1_xboole_0
      | k3_zfmisc_1(D_21,E_22,F_23) != k3_zfmisc_1(A_18,B_19,C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_188,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] :
      ( E_22 = B_19
      | k3_zfmisc_1(A_18,B_19,C_20) = '#skF_2'
      | k3_zfmisc_1(D_21,E_22,F_23) != k3_zfmisc_1(A_18,B_19,C_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_24])).

tff(c_12949,plain,(
    ! [C_513,A_510,C_511,B_514,C_509,A_508,B_512] :
      ( C_509 = B_514
      | k3_zfmisc_1(A_510,B_514,C_511) = '#skF_2'
      | k4_zfmisc_1(A_508,B_512,C_509,C_513) != k3_zfmisc_1(A_510,B_514,C_511) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_188])).

tff(c_13395,plain,(
    ! [B_521,A_522,C_523] :
      ( B_521 = '#skF_9'
      | k3_zfmisc_1(A_522,B_521,C_523) = '#skF_2'
      | k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') != k3_zfmisc_1(A_522,B_521,C_523) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5306,c_12949])).

tff(c_13449,plain,(
    ! [C_31,A_29,B_30,C_10] :
      ( C_31 = '#skF_9'
      | k3_zfmisc_1(k2_zfmisc_1(A_29,B_30),C_31,C_10) = '#skF_2'
      | k4_zfmisc_1(A_29,B_30,C_31,C_10) != k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_958,c_13395])).

tff(c_13460,plain,(
    ! [C_31,A_29,B_30,C_10] :
      ( C_31 = '#skF_9'
      | k4_zfmisc_1(A_29,B_30,C_31,C_10) = '#skF_2'
      | k4_zfmisc_1(A_29,B_30,C_31,C_10) != k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_13449])).

tff(c_13800,plain,
    ( '#skF_5' = '#skF_9'
    | k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13460])).

tff(c_13801,plain,(
    '#skF_5' = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_13800])).

tff(c_5289,plain,(
    k3_zfmisc_1('#skF_3','#skF_4','#skF_5') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5184])).

tff(c_5188,plain,
    ( '#skF_10' = '#skF_6'
    | '#skF_6' = '#skF_2'
    | k3_zfmisc_1('#skF_3','#skF_4','#skF_5') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_5180])).

tff(c_5291,plain,(
    k3_zfmisc_1('#skF_3','#skF_4','#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5188])).

tff(c_5300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5289,c_5291])).

tff(c_5302,plain,(
    k3_zfmisc_1('#skF_3','#skF_4','#skF_5') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5188])).

tff(c_13883,plain,(
    k3_zfmisc_1('#skF_3','#skF_4','#skF_9') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13801,c_5302])).

tff(c_5179,plain,(
    k3_zfmisc_1('#skF_7','#skF_8','#skF_9') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5163])).

tff(c_13882,plain,(
    k4_zfmisc_1('#skF_7','#skF_8','#skF_9','#skF_6') = k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13801,c_5306])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k1_relat_1(k2_zfmisc_1(A_6,B_7)) = A_6
      | k1_xboole_0 = B_7
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [A_6,B_7] :
      ( k1_relat_1(k2_zfmisc_1(A_6,B_7)) = A_6
      | B_7 = '#skF_2'
      | A_6 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_37,c_12])).

tff(c_21164,plain,(
    ! [A_661,B_662,C_663,D_664] :
      ( k1_relat_1(k4_zfmisc_1(A_661,B_662,C_663,D_664)) = k3_zfmisc_1(A_661,B_662,C_663)
      | D_664 = '#skF_2'
      | k3_zfmisc_1(A_661,B_662,C_663) = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_83])).

tff(c_21173,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6')) = k3_zfmisc_1('#skF_7','#skF_8','#skF_9')
    | '#skF_6' = '#skF_2'
    | k3_zfmisc_1('#skF_7','#skF_8','#skF_9') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_13882,c_21164])).

tff(c_21239,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6')) = k3_zfmisc_1('#skF_7','#skF_8','#skF_9')
    | '#skF_6' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_5179,c_21173])).

tff(c_21247,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_21239])).

tff(c_13889,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13801,c_50])).

tff(c_21253,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21247,c_13889])).

tff(c_21263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_21253])).

tff(c_21265,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_21239])).

tff(c_21264,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6')) = k3_zfmisc_1('#skF_7','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_21239])).

tff(c_133,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k1_relat_1(k4_zfmisc_1(A_42,B_43,C_44,D_45)) = k3_zfmisc_1(A_42,B_43,C_44)
      | D_45 = '#skF_2'
      | k3_zfmisc_1(A_42,B_43,C_44) = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_83])).

tff(c_21269,plain,
    ( k3_zfmisc_1('#skF_7','#skF_8','#skF_9') = k3_zfmisc_1('#skF_3','#skF_4','#skF_9')
    | '#skF_6' = '#skF_2'
    | k3_zfmisc_1('#skF_3','#skF_4','#skF_9') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_21264,c_133])).

tff(c_21275,plain,(
    k3_zfmisc_1('#skF_7','#skF_8','#skF_9') = k3_zfmisc_1('#skF_3','#skF_4','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_13883,c_21265,c_21269])).

tff(c_26,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] :
      ( D_21 = A_18
      | k3_zfmisc_1(A_18,B_19,C_20) = k1_xboole_0
      | k3_zfmisc_1(D_21,E_22,F_23) != k3_zfmisc_1(A_18,B_19,C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_269,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] :
      ( D_21 = A_18
      | k3_zfmisc_1(A_18,B_19,C_20) = '#skF_2'
      | k3_zfmisc_1(D_21,E_22,F_23) != k3_zfmisc_1(A_18,B_19,C_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_26])).

tff(c_21412,plain,(
    ! [D_21,E_22,F_23] :
      ( D_21 = '#skF_7'
      | k3_zfmisc_1('#skF_7','#skF_8','#skF_9') = '#skF_2'
      | k3_zfmisc_1(D_21,E_22,F_23) != k3_zfmisc_1('#skF_3','#skF_4','#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21275,c_269])).

tff(c_21434,plain,(
    ! [D_21,E_22,F_23] :
      ( D_21 = '#skF_7'
      | k3_zfmisc_1('#skF_3','#skF_4','#skF_9') = '#skF_2'
      | k3_zfmisc_1(D_21,E_22,F_23) != k3_zfmisc_1('#skF_3','#skF_4','#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21275,c_21412])).

tff(c_21435,plain,(
    ! [D_21,E_22,F_23] :
      ( D_21 = '#skF_7'
      | k3_zfmisc_1(D_21,E_22,F_23) != k3_zfmisc_1('#skF_3','#skF_4','#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_13883,c_21434])).

tff(c_21792,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_21435])).

tff(c_21794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_21792])).

tff(c_21795,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5288])).

tff(c_21807,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21795,c_50])).

tff(c_21818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_21807])).

tff(c_21819,plain,(
    '#skF_10' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5178])).

tff(c_18,plain,(
    ! [A_15,C_17,B_16] :
      ( r2_hidden(k2_mcart_1(A_15),C_17)
      | ~ r2_hidden(A_15,k2_zfmisc_1(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_690,plain,(
    ! [A_112,D_109,B_110,A_111,C_113] :
      ( r2_hidden(k2_mcart_1(A_112),D_109)
      | ~ r2_hidden(A_112,k4_zfmisc_1(A_111,B_110,C_113,D_109)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_18])).

tff(c_771,plain,(
    ! [A_121] :
      ( r2_hidden(k2_mcart_1(A_121),'#skF_10')
      | ~ r2_hidden(A_121,k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_690])).

tff(c_775,plain,(
    ! [A_121] :
      ( ~ v1_xboole_0('#skF_10')
      | ~ r2_hidden(A_121,k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_771,c_2])).

tff(c_891,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_775])).

tff(c_21821,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21819,c_891])).

tff(c_21826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_21821])).

tff(c_21827,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1109])).

tff(c_21880,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_21827,c_38])).

tff(c_21893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_21880])).

tff(c_21895,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_21908,plain,(
    '#skF_10' = '#skF_2' ),
    inference(resolution,[status(thm)],[c_21895,c_38])).

tff(c_21911,plain,(
    k4_zfmisc_1('#skF_7','#skF_8','#skF_9','#skF_2') = k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21908,c_32])).

tff(c_21914,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_21911])).

tff(c_21916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_21914])).

tff(c_21917,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_5' != '#skF_9'
    | '#skF_10' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_21923,plain,(
    '#skF_10' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_21917])).

tff(c_21918,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_21969,plain,(
    k4_zfmisc_1('#skF_3','#skF_8','#skF_9','#skF_10') = k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21918,c_32])).

tff(c_21995,plain,(
    ! [A_695,B_696,C_697,D_698] : k2_zfmisc_1(k3_zfmisc_1(A_695,B_696,C_697),D_698) = k4_zfmisc_1(A_695,B_696,C_697,D_698) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_21929,plain,(
    ! [A_6,B_7] :
      ( k2_relat_1(k2_zfmisc_1(A_6,B_7)) = B_7
      | B_7 = '#skF_2'
      | A_6 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_37,c_10])).

tff(c_28660,plain,(
    ! [A_1010,B_1011,C_1012,D_1013] :
      ( k2_relat_1(k4_zfmisc_1(A_1010,B_1011,C_1012,D_1013)) = D_1013
      | D_1013 = '#skF_2'
      | k3_zfmisc_1(A_1010,B_1011,C_1012) = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21995,c_21929])).

tff(c_28705,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_10'
    | '#skF_10' = '#skF_2'
    | k3_zfmisc_1('#skF_3','#skF_8','#skF_9') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_21969,c_28660])).

tff(c_28715,plain,(
    k3_zfmisc_1('#skF_3','#skF_8','#skF_9') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28705])).

tff(c_23269,plain,(
    ! [D_822,B_823,A_824,C_820,A_821] :
      ( r2_hidden(k1_mcart_1(A_824),k3_zfmisc_1(A_821,B_823,C_820))
      | ~ r2_hidden(A_824,k4_zfmisc_1(A_821,B_823,C_820,D_822)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21995,c_20])).

tff(c_23342,plain,(
    ! [A_833] :
      ( r2_hidden(k1_mcart_1(A_833),k3_zfmisc_1('#skF_3','#skF_8','#skF_9'))
      | ~ r2_hidden(A_833,k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21969,c_23269])).

tff(c_23352,plain,(
    ! [A_833] :
      ( ~ v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_8','#skF_9'))
      | ~ r2_hidden(A_833,k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_23342,c_2])).

tff(c_23777,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_23352])).

tff(c_28716,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28715,c_23777])).

tff(c_28720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_28716])).

tff(c_28721,plain,
    ( '#skF_10' = '#skF_2'
    | k2_relat_1(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_28705])).

tff(c_28723,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_28721])).

tff(c_22009,plain,(
    ! [A_695,B_696,C_697,D_698] :
      ( k2_relat_1(k4_zfmisc_1(A_695,B_696,C_697,D_698)) = D_698
      | D_698 = '#skF_2'
      | k3_zfmisc_1(A_695,B_696,C_697) = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21995,c_21929])).

tff(c_28727,plain,
    ( '#skF_10' = '#skF_6'
    | '#skF_6' = '#skF_2'
    | k3_zfmisc_1('#skF_3','#skF_4','#skF_5') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_28723,c_22009])).

tff(c_28733,plain,
    ( '#skF_6' = '#skF_2'
    | k3_zfmisc_1('#skF_3','#skF_4','#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_21923,c_28727])).

tff(c_28736,plain,(
    k3_zfmisc_1('#skF_3','#skF_4','#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28733])).

tff(c_28901,plain,(
    ! [D_14] : k4_zfmisc_1('#skF_3','#skF_4','#skF_5',D_14) = k2_zfmisc_1('#skF_2',D_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_28736,c_16])).

tff(c_28927,plain,(
    ! [D_14] : k4_zfmisc_1('#skF_3','#skF_4','#skF_5',D_14) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22069,c_28901])).

tff(c_28939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28927,c_50])).

tff(c_28940,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28733])).

tff(c_28951,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28940,c_50])).

tff(c_28962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22419,c_28951])).

tff(c_28963,plain,(
    '#skF_10' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28721])).

tff(c_22213,plain,(
    ! [D_742,A_744,A_741,B_743,C_740] :
      ( r2_hidden(k2_mcart_1(A_744),D_742)
      | ~ r2_hidden(A_744,k4_zfmisc_1(A_741,B_743,C_740,D_742)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21995,c_18])).

tff(c_22523,plain,(
    ! [A_768] :
      ( r2_hidden(k2_mcart_1(A_768),'#skF_10')
      | ~ r2_hidden(A_768,k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21969,c_22213])).

tff(c_22527,plain,(
    ! [A_768] :
      ( ~ v1_xboole_0('#skF_10')
      | ~ r2_hidden(A_768,k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_22523,c_2])).

tff(c_22700,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_22527])).

tff(c_28965,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28963,c_22700])).

tff(c_28971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_28965])).

tff(c_28973,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_23352])).

tff(c_29004,plain,(
    k3_zfmisc_1('#skF_3','#skF_8','#skF_9') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28973,c_38])).

tff(c_29044,plain,(
    ! [D_14] : k4_zfmisc_1('#skF_3','#skF_8','#skF_9',D_14) = k2_zfmisc_1('#skF_2',D_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_29004,c_16])).

tff(c_29056,plain,(
    ! [D_14] : k4_zfmisc_1('#skF_3','#skF_8','#skF_9',D_14) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22069,c_29044])).

tff(c_29058,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29056,c_21969])).

tff(c_29060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_29058])).

tff(c_29062,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_22527])).

tff(c_29078,plain,(
    '#skF_10' = '#skF_2' ),
    inference(resolution,[status(thm)],[c_29062,c_38])).

tff(c_29081,plain,(
    k4_zfmisc_1('#skF_3','#skF_8','#skF_9','#skF_2') = k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29078,c_21969])).

tff(c_29233,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22419,c_29081])).

tff(c_29236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_29233])).

tff(c_29238,plain,(
    '#skF_10' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_21917])).

tff(c_29244,plain,(
    k4_zfmisc_1('#skF_3','#skF_8','#skF_9','#skF_6') = k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29238,c_21918,c_32])).

tff(c_29315,plain,(
    ! [A_1045,B_1046,C_1047,D_1048] : k2_zfmisc_1(k3_zfmisc_1(A_1045,B_1046,C_1047),D_1048) = k4_zfmisc_1(A_1045,B_1046,C_1047,D_1048) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32105,plain,(
    ! [C_1236,D_1234,B_1235,A_1238,A_1237] :
      ( r2_hidden(k1_mcart_1(A_1237),k3_zfmisc_1(A_1238,B_1235,C_1236))
      | ~ r2_hidden(A_1237,k4_zfmisc_1(A_1238,B_1235,C_1236,D_1234)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29315,c_20])).

tff(c_32142,plain,(
    ! [A_1239] :
      ( r2_hidden(k1_mcart_1(A_1239),k3_zfmisc_1('#skF_3','#skF_8','#skF_9'))
      | ~ r2_hidden(A_1239,k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29244,c_32105])).

tff(c_32152,plain,(
    ! [A_1239] :
      ( ~ v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_8','#skF_9'))
      | ~ r2_hidden(A_1239,k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_32142,c_2])).

tff(c_32998,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_32152])).

tff(c_33005,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_8')) ),
    inference(resolution,[status(thm)],[c_29925,c_32998])).

tff(c_33014,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_29359,c_33005])).

tff(c_29285,plain,(
    ! [A_1038,B_1039,C_1040] : k2_zfmisc_1(k2_zfmisc_1(A_1038,B_1039),C_1040) = k3_zfmisc_1(A_1038,B_1039,C_1040) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_29304,plain,(
    ! [A_8,B_9,C_10,C_1040] : k3_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10,C_1040) = k2_zfmisc_1(k3_zfmisc_1(A_8,B_9,C_10),C_1040) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_29285])).

tff(c_30059,plain,(
    ! [A_8,B_9,C_10,C_1040] : k3_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10,C_1040) = k4_zfmisc_1(A_8,B_9,C_10,C_1040) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_29304])).

tff(c_29741,plain,(
    ! [B_16,C_17,C_1110] :
      ( r2_hidden(k1_mcart_1(k1_mcart_1('#skF_1'(k2_zfmisc_1(k2_zfmisc_1(B_16,C_17),C_1110)))),B_16)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_16,C_17),C_1110)) ) ),
    inference(resolution,[status(thm)],[c_29728,c_20])).

tff(c_34275,plain,(
    ! [B_1311,C_1312,C_1313] :
      ( r2_hidden(k1_mcart_1(k1_mcart_1('#skF_1'(k3_zfmisc_1(B_1311,C_1312,C_1313)))),B_1311)
      | v1_xboole_0(k3_zfmisc_1(B_1311,C_1312,C_1313)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_29741])).

tff(c_34359,plain,(
    ! [B_1314,C_1315,C_1316] :
      ( ~ v1_xboole_0(B_1314)
      | v1_xboole_0(k3_zfmisc_1(B_1314,C_1315,C_1316)) ) ),
    inference(resolution,[status(thm)],[c_34275,c_2])).

tff(c_34413,plain,(
    ! [A_8,B_9,C_10,C_1040] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | v1_xboole_0(k4_zfmisc_1(A_8,B_9,C_10,C_1040)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30059,c_34359])).

tff(c_29301,plain,(
    ! [A_15,C_1040,A_1038,B_1039] :
      ( r2_hidden(k2_mcart_1(A_15),C_1040)
      | ~ r2_hidden(A_15,k3_zfmisc_1(A_1038,B_1039,C_1040)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29285,c_18])).

tff(c_29738,plain,(
    ! [A_1038,B_1039,C_1040,C_1110] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1'(k2_zfmisc_1(k3_zfmisc_1(A_1038,B_1039,C_1040),C_1110)))),C_1040)
      | v1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(A_1038,B_1039,C_1040),C_1110)) ) ),
    inference(resolution,[status(thm)],[c_29728,c_29301])).

tff(c_45835,plain,(
    ! [A_1583,B_1584,C_1585,C_1586] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1'(k4_zfmisc_1(A_1583,B_1584,C_1585,C_1586)))),C_1585)
      | v1_xboole_0(k4_zfmisc_1(A_1583,B_1584,C_1585,C_1586)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_29738])).

tff(c_45926,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1'(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')))),'#skF_9')
    | v1_xboole_0(k4_zfmisc_1('#skF_3','#skF_8','#skF_9','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29244,c_45835])).

tff(c_45943,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1'(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')))),'#skF_9')
    | v1_xboole_0(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29244,c_45926])).

tff(c_46821,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_45943])).

tff(c_46842,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46821,c_38])).

tff(c_46855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46842])).

tff(c_46857,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_45943])).

tff(c_46871,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_34413,c_46857])).

tff(c_46881,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_29359,c_46871])).

tff(c_29768,plain,(
    ! [B_1109,C_1110] :
      ( ~ v1_xboole_0(B_1109)
      | v1_xboole_0(k2_zfmisc_1(B_1109,C_1110)) ) ),
    inference(resolution,[status(thm)],[c_29728,c_2])).

tff(c_33013,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_29768,c_33005])).

tff(c_30060,plain,(
    ! [A_1127,B_1128,C_1129,C_1130] : k3_zfmisc_1(k2_zfmisc_1(A_1127,B_1128),C_1129,C_1130) = k4_zfmisc_1(A_1127,B_1128,C_1129,C_1130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_29304])).

tff(c_29362,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] :
      ( E_22 = B_19
      | k3_zfmisc_1(A_18,B_19,C_20) = '#skF_2'
      | k3_zfmisc_1(D_21,E_22,F_23) != k3_zfmisc_1(A_18,B_19,C_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_24])).

tff(c_30092,plain,(
    ! [E_22,D_21,A_1127,C_1129,F_23,B_1128,C_1130] :
      ( E_22 = C_1129
      | k3_zfmisc_1(k2_zfmisc_1(A_1127,B_1128),C_1129,C_1130) = '#skF_2'
      | k4_zfmisc_1(A_1127,B_1128,C_1129,C_1130) != k3_zfmisc_1(D_21,E_22,F_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30060,c_29362])).

tff(c_53656,plain,(
    ! [A_1742,F_1740,C_1737,E_1739,B_1736,C_1738,D_1741] :
      ( E_1739 = C_1737
      | k4_zfmisc_1(A_1742,B_1736,C_1737,C_1738) = '#skF_2'
      | k4_zfmisc_1(A_1742,B_1736,C_1737,C_1738) != k3_zfmisc_1(D_1741,E_1739,F_1740) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30059,c_30092])).

tff(c_53803,plain,(
    ! [E_1739,D_1741,F_1740] :
      ( E_1739 = '#skF_9'
      | k4_zfmisc_1('#skF_3','#skF_8','#skF_9','#skF_6') = '#skF_2'
      | k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') != k3_zfmisc_1(D_1741,E_1739,F_1740) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29244,c_53656])).

tff(c_53810,plain,(
    ! [E_1739,D_1741,F_1740] :
      ( E_1739 = '#skF_9'
      | k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') = '#skF_2'
      | k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') != k3_zfmisc_1(D_1741,E_1739,F_1740) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29244,c_53803])).

tff(c_53812,plain,(
    ! [E_1743,D_1744,F_1745] :
      ( E_1743 = '#skF_9'
      | k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') != k3_zfmisc_1(D_1744,E_1743,F_1745) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_53810])).

tff(c_53884,plain,(
    ! [C_10,A_8,B_9,C_1040] :
      ( C_10 = '#skF_9'
      | k4_zfmisc_1(A_8,B_9,C_10,C_1040) != k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30059,c_53812])).

tff(c_54107,plain,(
    '#skF_5' = '#skF_9' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_53884])).

tff(c_54194,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54107,c_50])).

tff(c_54193,plain,(
    k4_zfmisc_1('#skF_3','#skF_8','#skF_9','#skF_6') = k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54107,c_29244])).

tff(c_29487,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] :
      ( D_21 = A_18
      | k3_zfmisc_1(A_18,B_19,C_20) = '#skF_2'
      | k3_zfmisc_1(D_21,E_22,F_23) != k3_zfmisc_1(A_18,B_19,C_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_26])).

tff(c_30073,plain,(
    ! [E_22,D_21,A_1127,C_1129,F_23,B_1128,C_1130] :
      ( k2_zfmisc_1(A_1127,B_1128) = D_21
      | k3_zfmisc_1(k2_zfmisc_1(A_1127,B_1128),C_1129,C_1130) = '#skF_2'
      | k4_zfmisc_1(A_1127,B_1128,C_1129,C_1130) != k3_zfmisc_1(D_21,E_22,F_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30060,c_29487])).

tff(c_64802,plain,(
    ! [B_1951,D_1956,F_1955,A_1957,C_1953,E_1954,C_1952] :
      ( k2_zfmisc_1(A_1957,B_1951) = D_1956
      | k4_zfmisc_1(A_1957,B_1951,C_1952,C_1953) = '#skF_2'
      | k4_zfmisc_1(A_1957,B_1951,C_1952,C_1953) != k3_zfmisc_1(D_1956,E_1954,F_1955) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30059,c_30073])).

tff(c_64832,plain,(
    ! [D_1956,E_1954,F_1955] :
      ( k2_zfmisc_1('#skF_3','#skF_8') = D_1956
      | k4_zfmisc_1('#skF_3','#skF_8','#skF_9','#skF_6') = '#skF_2'
      | k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') != k3_zfmisc_1(D_1956,E_1954,F_1955) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54193,c_64802])).

tff(c_64977,plain,(
    ! [D_1956,E_1954,F_1955] :
      ( k2_zfmisc_1('#skF_3','#skF_8') = D_1956
      | k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') = '#skF_2'
      | k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') != k3_zfmisc_1(D_1956,E_1954,F_1955) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54193,c_64832])).

tff(c_67002,plain,(
    ! [D_1976,E_1977,F_1978] :
      ( k2_zfmisc_1('#skF_3','#skF_8') = D_1976
      | k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') != k3_zfmisc_1(D_1976,E_1977,F_1978) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54194,c_64977])).

tff(c_67092,plain,(
    ! [A_8,B_9,C_10,C_1040] :
      ( k2_zfmisc_1(A_8,B_9) = k2_zfmisc_1('#skF_3','#skF_8')
      | k4_zfmisc_1(A_8,B_9,C_10,C_1040) != k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30059,c_67002])).

tff(c_94833,plain,(
    k2_zfmisc_1('#skF_3','#skF_8') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_67092])).

tff(c_29272,plain,(
    ! [A_6,B_7] :
      ( k2_relat_1(k2_zfmisc_1(A_6,B_7)) = B_7
      | B_7 = '#skF_2'
      | A_6 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_37,c_10])).

tff(c_95190,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) = '#skF_8'
    | '#skF_2' = '#skF_8'
    | '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_94833,c_29272])).

tff(c_96038,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_95190])).

tff(c_96190,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96038,c_8])).

tff(c_96192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33013,c_96190])).

tff(c_96194,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_95190])).

tff(c_29237,plain,
    ( '#skF_5' != '#skF_9'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_21917])).

tff(c_29243,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_29237])).

tff(c_96193,plain,
    ( '#skF_2' = '#skF_8'
    | k2_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_95190])).

tff(c_96196,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_96193])).

tff(c_96200,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_96196,c_29272])).

tff(c_96206,plain,(
    '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_96194,c_29243,c_96200])).

tff(c_96361,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96206,c_8])).

tff(c_96363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46881,c_96361])).

tff(c_96364,plain,(
    '#skF_2' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_96193])).

tff(c_96518,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96364,c_8])).

tff(c_96520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33014,c_96518])).

tff(c_96522,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_32152])).

tff(c_96553,plain,(
    k3_zfmisc_1('#skF_3','#skF_8','#skF_9') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_96522,c_38])).

tff(c_96605,plain,(
    ! [D_14] : k4_zfmisc_1('#skF_3','#skF_8','#skF_9',D_14) = k2_zfmisc_1('#skF_2',D_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_96553,c_16])).

tff(c_96620,plain,(
    ! [D_14] : k4_zfmisc_1('#skF_3','#skF_8','#skF_9',D_14) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29791,c_96605])).

tff(c_96622,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96620,c_29244])).

tff(c_96624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_96622])).

tff(c_96625,plain,(
    ! [B_1088] : ~ v1_xboole_0(B_1088) ),
    inference(splitRight,[status(thm)],[c_29576])).

tff(c_96631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96625,c_8])).

tff(c_96633,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_29237])).

tff(c_96634,plain,(
    k4_zfmisc_1('#skF_3','#skF_8','#skF_9','#skF_6') = k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21918,c_29238,c_32])).

tff(c_96639,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') = k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96633,c_96634])).

tff(c_96705,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96639,c_50])).

tff(c_96632,plain,(
    '#skF_5' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_29237])).

tff(c_96680,plain,(
    ! [A_2306,B_2307,C_2308] : k2_zfmisc_1(k2_zfmisc_1(A_2306,B_2307),C_2308) = k3_zfmisc_1(A_2306,B_2307,C_2308) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96683,plain,(
    ! [A_2306,B_2307,C_2308,C_10] : k3_zfmisc_1(k2_zfmisc_1(A_2306,B_2307),C_2308,C_10) = k2_zfmisc_1(k3_zfmisc_1(A_2306,B_2307,C_2308),C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_96680,c_14])).

tff(c_97759,plain,(
    ! [A_2306,B_2307,C_2308,C_10] : k3_zfmisc_1(k2_zfmisc_1(A_2306,B_2307),C_2308,C_10) = k4_zfmisc_1(A_2306,B_2307,C_2308,C_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_96683])).

tff(c_97760,plain,(
    ! [A_2411,B_2412,C_2413,C_2414] : k3_zfmisc_1(k2_zfmisc_1(A_2411,B_2412),C_2413,C_2414) = k4_zfmisc_1(A_2411,B_2412,C_2413,C_2414) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_96683])).

tff(c_96860,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] :
      ( E_22 = B_19
      | k3_zfmisc_1(A_18,B_19,C_20) = '#skF_2'
      | k3_zfmisc_1(D_21,E_22,F_23) != k3_zfmisc_1(A_18,B_19,C_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_24])).

tff(c_118203,plain,(
    ! [A_2940,C_2937,C_2936,B_2942,C_2939,A_2938,B_2941] :
      ( C_2937 = B_2942
      | k3_zfmisc_1(A_2938,B_2942,C_2939) = '#skF_2'
      | k4_zfmisc_1(A_2940,B_2941,C_2937,C_2936) != k3_zfmisc_1(A_2938,B_2942,C_2939) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97760,c_96860])).

tff(c_119289,plain,(
    ! [B_2953,A_2954,C_2955] :
      ( B_2953 = '#skF_5'
      | k3_zfmisc_1(A_2954,B_2953,C_2955) = '#skF_2'
      | k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') != k3_zfmisc_1(A_2954,B_2953,C_2955) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96639,c_118203])).

tff(c_119355,plain,(
    ! [C_2308,A_2306,B_2307,C_10] :
      ( C_2308 = '#skF_5'
      | k3_zfmisc_1(k2_zfmisc_1(A_2306,B_2307),C_2308,C_10) = '#skF_2'
      | k4_zfmisc_1(A_2306,B_2307,C_2308,C_10) != k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97759,c_119289])).

tff(c_119369,plain,(
    ! [C_2308,A_2306,B_2307,C_10] :
      ( C_2308 = '#skF_5'
      | k4_zfmisc_1(A_2306,B_2307,C_2308,C_10) = '#skF_2'
      | k4_zfmisc_1(A_2306,B_2307,C_2308,C_10) != k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97759,c_119355])).

tff(c_120587,plain,
    ( '#skF_5' = '#skF_9'
    | k4_zfmisc_1('#skF_3','#skF_4','#skF_9','#skF_6') = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_119369])).

tff(c_120589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96705,c_96632,c_120587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:34:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.65/10.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.73/10.63  
% 18.73/10.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.73/10.63  %$ r2_hidden > v1_xboole_0 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4
% 18.73/10.63  
% 18.73/10.63  %Foreground sorts:
% 18.73/10.63  
% 18.73/10.63  
% 18.73/10.63  %Background operators:
% 18.73/10.63  
% 18.73/10.63  
% 18.73/10.63  %Foreground operators:
% 18.73/10.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.73/10.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.73/10.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 18.73/10.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.73/10.63  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 18.73/10.63  tff('#skF_7', type, '#skF_7': $i).
% 18.73/10.63  tff('#skF_10', type, '#skF_10': $i).
% 18.73/10.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.73/10.63  tff('#skF_5', type, '#skF_5': $i).
% 18.73/10.63  tff('#skF_6', type, '#skF_6': $i).
% 18.73/10.63  tff('#skF_2', type, '#skF_2': $i).
% 18.73/10.63  tff('#skF_3', type, '#skF_3': $i).
% 18.73/10.63  tff('#skF_9', type, '#skF_9': $i).
% 18.73/10.63  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 18.73/10.63  tff('#skF_8', type, '#skF_8': $i).
% 18.73/10.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.73/10.63  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 18.73/10.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 18.73/10.63  tff('#skF_4', type, '#skF_4': $i).
% 18.73/10.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.73/10.63  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 18.73/10.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 18.73/10.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.73/10.63  
% 18.90/10.67  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 18.90/10.67  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 18.90/10.67  tff(f_82, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_mcart_1)).
% 18.90/10.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 18.90/10.67  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 18.90/10.67  tff(f_51, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 18.90/10.67  tff(f_53, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 18.90/10.67  tff(f_49, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 18.90/10.67  tff(f_69, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 18.90/10.67  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.90/10.67  tff(c_33, plain, (![A_24]: (k1_xboole_0=A_24 | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.90/10.67  tff(c_37, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_33])).
% 18.90/10.67  tff(c_30, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 18.90/10.67  tff(c_50, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_37, c_30])).
% 18.90/10.67  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.90/10.67  tff(c_29254, plain, (![A_1031, B_1032, C_1033]: (r2_hidden(k1_mcart_1(A_1031), B_1032) | ~r2_hidden(A_1031, k2_zfmisc_1(B_1032, C_1033)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.90/10.67  tff(c_29728, plain, (![B_1109, C_1110]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1109, C_1110))), B_1109) | v1_xboole_0(k2_zfmisc_1(B_1109, C_1110)))), inference(resolution, [status(thm)], [c_4, c_29254])).
% 18.90/10.67  tff(c_29249, plain, (![A_1028, C_1029, B_1030]: (r2_hidden(k2_mcart_1(A_1028), C_1029) | ~r2_hidden(A_1028, k2_zfmisc_1(B_1030, C_1029)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.90/10.67  tff(c_29337, plain, (![B_1049, C_1050]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1049, C_1050))), C_1050) | v1_xboole_0(k2_zfmisc_1(B_1049, C_1050)))), inference(resolution, [status(thm)], [c_4, c_29249])).
% 18.90/10.67  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.90/10.67  tff(c_29368, plain, (![C_1057, B_1058]: (~v1_xboole_0(C_1057) | v1_xboole_0(k2_zfmisc_1(B_1058, C_1057)))), inference(resolution, [status(thm)], [c_29337, c_2])).
% 18.90/10.67  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.90/10.67  tff(c_38, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_6])).
% 18.90/10.67  tff(c_29379, plain, (![B_1059, C_1060]: (k2_zfmisc_1(B_1059, C_1060)='#skF_2' | ~v1_xboole_0(C_1060))), inference(resolution, [status(thm)], [c_29368, c_38])).
% 18.90/10.67  tff(c_29386, plain, (![B_1061]: (k2_zfmisc_1(B_1061, '#skF_2')='#skF_2')), inference(resolution, [status(thm)], [c_8, c_29379])).
% 18.90/10.67  tff(c_20, plain, (![A_15, B_16, C_17]: (r2_hidden(k1_mcart_1(A_15), B_16) | ~r2_hidden(A_15, k2_zfmisc_1(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.90/10.67  tff(c_29560, plain, (![A_1087, B_1088]: (r2_hidden(k1_mcart_1(A_1087), B_1088) | ~r2_hidden(A_1087, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_29386, c_20])).
% 18.90/10.67  tff(c_29576, plain, (![B_1088, A_1087]: (~v1_xboole_0(B_1088) | ~r2_hidden(A_1087, '#skF_2'))), inference(resolution, [status(thm)], [c_29560, c_2])).
% 18.90/10.67  tff(c_29577, plain, (![A_1087]: (~r2_hidden(A_1087, '#skF_2'))), inference(splitLeft, [status(thm)], [c_29576])).
% 18.90/10.67  tff(c_29772, plain, (![C_1111]: (v1_xboole_0(k2_zfmisc_1('#skF_2', C_1111)))), inference(resolution, [status(thm)], [c_29728, c_29577])).
% 18.90/10.67  tff(c_29791, plain, (![C_1111]: (k2_zfmisc_1('#skF_2', C_1111)='#skF_2')), inference(resolution, [status(thm)], [c_29772, c_38])).
% 18.90/10.67  tff(c_29359, plain, (![C_1050, B_1049]: (~v1_xboole_0(C_1050) | v1_xboole_0(k2_zfmisc_1(B_1049, C_1050)))), inference(resolution, [status(thm)], [c_29337, c_2])).
% 18.90/10.67  tff(c_14, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.90/10.67  tff(c_29901, plain, (![B_1115, C_1116]: (~v1_xboole_0(B_1115) | v1_xboole_0(k2_zfmisc_1(B_1115, C_1116)))), inference(resolution, [status(thm)], [c_29728, c_2])).
% 18.90/10.67  tff(c_29925, plain, (![A_8, B_9, C_10]: (~v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | v1_xboole_0(k3_zfmisc_1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_29901])).
% 18.90/10.67  tff(c_21942, plain, (![A_683, C_684, B_685]: (r2_hidden(k2_mcart_1(A_683), C_684) | ~r2_hidden(A_683, k2_zfmisc_1(B_685, C_684)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.90/10.67  tff(c_22319, plain, (![B_762, C_763]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_762, C_763))), C_763) | v1_xboole_0(k2_zfmisc_1(B_762, C_763)))), inference(resolution, [status(thm)], [c_4, c_21942])).
% 18.90/10.67  tff(c_21924, plain, (![A_678, B_679, C_680]: (r2_hidden(k1_mcart_1(A_678), B_679) | ~r2_hidden(A_678, k2_zfmisc_1(B_679, C_680)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.90/10.67  tff(c_22017, plain, (![B_699, C_700]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_699, C_700))), B_699) | v1_xboole_0(k2_zfmisc_1(B_699, C_700)))), inference(resolution, [status(thm)], [c_4, c_21924])).
% 18.90/10.67  tff(c_22045, plain, (![B_701, C_702]: (~v1_xboole_0(B_701) | v1_xboole_0(k2_zfmisc_1(B_701, C_702)))), inference(resolution, [status(thm)], [c_22017, c_2])).
% 18.90/10.67  tff(c_22062, plain, (![B_709, C_710]: (k2_zfmisc_1(B_709, C_710)='#skF_2' | ~v1_xboole_0(B_709))), inference(resolution, [status(thm)], [c_22045, c_38])).
% 18.90/10.67  tff(c_22070, plain, (![C_711]: (k2_zfmisc_1('#skF_2', C_711)='#skF_2')), inference(resolution, [status(thm)], [c_8, c_22062])).
% 18.90/10.67  tff(c_22150, plain, (![A_726]: (r2_hidden(k1_mcart_1(A_726), '#skF_2') | ~r2_hidden(A_726, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_22070, c_20])).
% 18.90/10.67  tff(c_22153, plain, (![A_726]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_726, '#skF_2'))), inference(resolution, [status(thm)], [c_22150, c_2])).
% 18.90/10.67  tff(c_22156, plain, (![A_726]: (~r2_hidden(A_726, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_22153])).
% 18.90/10.67  tff(c_22357, plain, (![B_764]: (v1_xboole_0(k2_zfmisc_1(B_764, '#skF_2')))), inference(resolution, [status(thm)], [c_22319, c_22156])).
% 18.90/10.67  tff(c_22391, plain, (![B_765]: (k2_zfmisc_1(B_765, '#skF_2')='#skF_2')), inference(resolution, [status(thm)], [c_22357, c_38])).
% 18.90/10.67  tff(c_16, plain, (![A_11, B_12, C_13, D_14]: (k2_zfmisc_1(k3_zfmisc_1(A_11, B_12, C_13), D_14)=k4_zfmisc_1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.90/10.67  tff(c_22419, plain, (![A_11, B_12, C_13]: (k4_zfmisc_1(A_11, B_12, C_13, '#skF_2')='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22391, c_16])).
% 18.90/10.67  tff(c_22069, plain, (![C_710]: (k2_zfmisc_1('#skF_2', C_710)='#skF_2')), inference(resolution, [status(thm)], [c_8, c_22062])).
% 18.90/10.67  tff(c_76, plain, (![A_32, C_33, B_34]: (r2_hidden(k2_mcart_1(A_32), C_33) | ~r2_hidden(A_32, k2_zfmisc_1(B_34, C_33)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.90/10.67  tff(c_405, plain, (![B_99, C_100]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_99, C_100))), C_100) | v1_xboole_0(k2_zfmisc_1(B_99, C_100)))), inference(resolution, [status(thm)], [c_4, c_76])).
% 18.90/10.67  tff(c_115, plain, (![A_39, B_40, C_41]: (r2_hidden(k1_mcart_1(A_39), B_40) | ~r2_hidden(A_39, k2_zfmisc_1(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.90/10.67  tff(c_149, plain, (![B_50, C_51]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_50, C_51))), B_50) | v1_xboole_0(k2_zfmisc_1(B_50, C_51)))), inference(resolution, [status(thm)], [c_4, c_115])).
% 18.90/10.67  tff(c_177, plain, (![B_52, C_53]: (~v1_xboole_0(B_52) | v1_xboole_0(k2_zfmisc_1(B_52, C_53)))), inference(resolution, [status(thm)], [c_149, c_2])).
% 18.90/10.67  tff(c_194, plain, (![B_60, C_61]: (k2_zfmisc_1(B_60, C_61)='#skF_2' | ~v1_xboole_0(B_60))), inference(resolution, [status(thm)], [c_177, c_38])).
% 18.90/10.67  tff(c_202, plain, (![C_62]: (k2_zfmisc_1('#skF_2', C_62)='#skF_2')), inference(resolution, [status(thm)], [c_8, c_194])).
% 18.90/10.67  tff(c_282, plain, (![A_77]: (r2_hidden(k1_mcart_1(A_77), '#skF_2') | ~r2_hidden(A_77, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_20])).
% 18.90/10.67  tff(c_285, plain, (![A_77]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_77, '#skF_2'))), inference(resolution, [status(thm)], [c_282, c_2])).
% 18.90/10.67  tff(c_288, plain, (![A_77]: (~r2_hidden(A_77, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_285])).
% 18.90/10.67  tff(c_439, plain, (![B_101]: (v1_xboole_0(k2_zfmisc_1(B_101, '#skF_2')))), inference(resolution, [status(thm)], [c_405, c_288])).
% 18.90/10.67  tff(c_470, plain, (![B_102]: (k2_zfmisc_1(B_102, '#skF_2')='#skF_2')), inference(resolution, [status(thm)], [c_439, c_38])).
% 18.90/10.67  tff(c_495, plain, (![A_11, B_12, C_13]: (k4_zfmisc_1(A_11, B_12, C_13, '#skF_2')='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_470, c_16])).
% 18.90/10.67  tff(c_28, plain, ('#skF_10'!='#skF_6' | '#skF_5'!='#skF_9' | '#skF_8'!='#skF_4' | '#skF_7'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 18.90/10.67  tff(c_56, plain, ('#skF_7'!='#skF_3'), inference(splitLeft, [status(thm)], [c_28])).
% 18.90/10.67  tff(c_61, plain, (![A_29, B_30, C_31]: (k2_zfmisc_1(k2_zfmisc_1(A_29, B_30), C_31)=k3_zfmisc_1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.90/10.67  tff(c_64, plain, (![A_29, B_30, C_31, C_10]: (k3_zfmisc_1(k2_zfmisc_1(A_29, B_30), C_31, C_10)=k2_zfmisc_1(k3_zfmisc_1(A_29, B_30, C_31), C_10))), inference(superposition, [status(thm), theory('equality')], [c_61, c_14])).
% 18.90/10.67  tff(c_958, plain, (![A_29, B_30, C_31, C_10]: (k3_zfmisc_1(k2_zfmisc_1(A_29, B_30), C_31, C_10)=k4_zfmisc_1(A_29, B_30, C_31, C_10))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_64])).
% 18.90/10.67  tff(c_201, plain, (![C_61]: (k2_zfmisc_1('#skF_2', C_61)='#skF_2')), inference(resolution, [status(thm)], [c_8, c_194])).
% 18.90/10.67  tff(c_32, plain, (k4_zfmisc_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 18.90/10.67  tff(c_122, plain, (![A_42, B_43, C_44, D_45]: (k2_zfmisc_1(k3_zfmisc_1(A_42, B_43, C_44), D_45)=k4_zfmisc_1(A_42, B_43, C_44, D_45))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.90/10.67  tff(c_10, plain, (![A_6, B_7]: (k2_relat_1(k2_zfmisc_1(A_6, B_7))=B_7 | k1_xboole_0=B_7 | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.90/10.67  tff(c_99, plain, (![A_6, B_7]: (k2_relat_1(k2_zfmisc_1(A_6, B_7))=B_7 | B_7='#skF_2' | A_6='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_37, c_10])).
% 18.90/10.67  tff(c_5121, plain, (![A_313, B_314, C_315, D_316]: (k2_relat_1(k4_zfmisc_1(A_313, B_314, C_315, D_316))=D_316 | D_316='#skF_2' | k3_zfmisc_1(A_313, B_314, C_315)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_122, c_99])).
% 18.90/10.67  tff(c_5163, plain, (k2_relat_1(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_10' | '#skF_10'='#skF_2' | k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_32, c_5121])).
% 18.90/10.67  tff(c_5171, plain, (k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')='#skF_2'), inference(splitLeft, [status(thm)], [c_5163])).
% 18.90/10.67  tff(c_1081, plain, (![A_152, B_153, C_154, D_155]: (~v1_xboole_0(k3_zfmisc_1(A_152, B_153, C_154)) | v1_xboole_0(k4_zfmisc_1(A_152, B_153, C_154, D_155)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_177])).
% 18.90/10.67  tff(c_1109, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | v1_xboole_0(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1081])).
% 18.90/10.67  tff(c_1424, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_1109])).
% 18.90/10.67  tff(c_5173, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5171, c_1424])).
% 18.90/10.67  tff(c_5177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_5173])).
% 18.90/10.67  tff(c_5178, plain, ('#skF_10'='#skF_2' | k2_relat_1(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_10'), inference(splitRight, [status(thm)], [c_5163])).
% 18.90/10.67  tff(c_5180, plain, (k2_relat_1(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_10'), inference(splitLeft, [status(thm)], [c_5178])).
% 18.90/10.67  tff(c_130, plain, (![A_42, B_43, C_44, D_45]: (k2_relat_1(k4_zfmisc_1(A_42, B_43, C_44, D_45))=D_45 | D_45='#skF_2' | k3_zfmisc_1(A_42, B_43, C_44)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_122, c_99])).
% 18.90/10.67  tff(c_5184, plain, ('#skF_10'='#skF_6' | '#skF_6'='#skF_2' | k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_5180, c_130])).
% 18.90/10.67  tff(c_5191, plain, (k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_5184])).
% 18.90/10.67  tff(c_5257, plain, (![D_14]: (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', D_14)=k2_zfmisc_1('#skF_2', D_14))), inference(superposition, [status(thm), theory('equality')], [c_5191, c_16])).
% 18.90/10.67  tff(c_5275, plain, (![D_14]: (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', D_14)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_5257])).
% 18.90/10.67  tff(c_5287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5275, c_50])).
% 18.90/10.67  tff(c_5288, plain, ('#skF_6'='#skF_2' | '#skF_10'='#skF_6'), inference(splitRight, [status(thm)], [c_5184])).
% 18.90/10.67  tff(c_5290, plain, ('#skF_10'='#skF_6'), inference(splitLeft, [status(thm)], [c_5288])).
% 18.90/10.67  tff(c_5306, plain, (k4_zfmisc_1('#skF_7', '#skF_8', '#skF_9', '#skF_6')=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5290, c_32])).
% 18.90/10.67  tff(c_960, plain, (![A_144, B_145, C_146, C_147]: (k3_zfmisc_1(k2_zfmisc_1(A_144, B_145), C_146, C_147)=k4_zfmisc_1(A_144, B_145, C_146, C_147))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_64])).
% 18.90/10.67  tff(c_24, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (E_22=B_19 | k3_zfmisc_1(A_18, B_19, C_20)=k1_xboole_0 | k3_zfmisc_1(D_21, E_22, F_23)!=k3_zfmisc_1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 18.90/10.67  tff(c_188, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (E_22=B_19 | k3_zfmisc_1(A_18, B_19, C_20)='#skF_2' | k3_zfmisc_1(D_21, E_22, F_23)!=k3_zfmisc_1(A_18, B_19, C_20))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_24])).
% 18.90/10.67  tff(c_12949, plain, (![C_513, A_510, C_511, B_514, C_509, A_508, B_512]: (C_509=B_514 | k3_zfmisc_1(A_510, B_514, C_511)='#skF_2' | k4_zfmisc_1(A_508, B_512, C_509, C_513)!=k3_zfmisc_1(A_510, B_514, C_511))), inference(superposition, [status(thm), theory('equality')], [c_960, c_188])).
% 18.90/10.67  tff(c_13395, plain, (![B_521, A_522, C_523]: (B_521='#skF_9' | k3_zfmisc_1(A_522, B_521, C_523)='#skF_2' | k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k3_zfmisc_1(A_522, B_521, C_523))), inference(superposition, [status(thm), theory('equality')], [c_5306, c_12949])).
% 18.90/10.67  tff(c_13449, plain, (![C_31, A_29, B_30, C_10]: (C_31='#skF_9' | k3_zfmisc_1(k2_zfmisc_1(A_29, B_30), C_31, C_10)='#skF_2' | k4_zfmisc_1(A_29, B_30, C_31, C_10)!=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_958, c_13395])).
% 18.90/10.67  tff(c_13460, plain, (![C_31, A_29, B_30, C_10]: (C_31='#skF_9' | k4_zfmisc_1(A_29, B_30, C_31, C_10)='#skF_2' | k4_zfmisc_1(A_29, B_30, C_31, C_10)!=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_13449])).
% 18.90/10.67  tff(c_13800, plain, ('#skF_5'='#skF_9' | k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_13460])).
% 18.90/10.67  tff(c_13801, plain, ('#skF_5'='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_50, c_13800])).
% 18.90/10.67  tff(c_5289, plain, (k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')!='#skF_2'), inference(splitRight, [status(thm)], [c_5184])).
% 18.90/10.67  tff(c_5188, plain, ('#skF_10'='#skF_6' | '#skF_6'='#skF_2' | k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_130, c_5180])).
% 18.90/10.67  tff(c_5291, plain, (k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_5188])).
% 18.90/10.67  tff(c_5300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5289, c_5291])).
% 18.90/10.67  tff(c_5302, plain, (k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')!='#skF_2'), inference(splitRight, [status(thm)], [c_5188])).
% 18.90/10.67  tff(c_13883, plain, (k3_zfmisc_1('#skF_3', '#skF_4', '#skF_9')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13801, c_5302])).
% 18.90/10.67  tff(c_5179, plain, (k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')!='#skF_2'), inference(splitRight, [status(thm)], [c_5163])).
% 18.90/10.67  tff(c_13882, plain, (k4_zfmisc_1('#skF_7', '#skF_8', '#skF_9', '#skF_6')=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13801, c_5306])).
% 18.90/10.67  tff(c_12, plain, (![A_6, B_7]: (k1_relat_1(k2_zfmisc_1(A_6, B_7))=A_6 | k1_xboole_0=B_7 | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.90/10.67  tff(c_83, plain, (![A_6, B_7]: (k1_relat_1(k2_zfmisc_1(A_6, B_7))=A_6 | B_7='#skF_2' | A_6='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_37, c_12])).
% 18.90/10.67  tff(c_21164, plain, (![A_661, B_662, C_663, D_664]: (k1_relat_1(k4_zfmisc_1(A_661, B_662, C_663, D_664))=k3_zfmisc_1(A_661, B_662, C_663) | D_664='#skF_2' | k3_zfmisc_1(A_661, B_662, C_663)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_122, c_83])).
% 18.90/10.67  tff(c_21173, plain, (k1_relat_1(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6'))=k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9') | '#skF_6'='#skF_2' | k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_13882, c_21164])).
% 18.90/10.67  tff(c_21239, plain, (k1_relat_1(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6'))=k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9') | '#skF_6'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_5179, c_21173])).
% 18.90/10.67  tff(c_21247, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_21239])).
% 18.90/10.67  tff(c_13889, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13801, c_50])).
% 18.90/10.67  tff(c_21253, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_21247, c_13889])).
% 18.90/10.67  tff(c_21263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_495, c_21253])).
% 18.90/10.67  tff(c_21265, plain, ('#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_21239])).
% 18.90/10.67  tff(c_21264, plain, (k1_relat_1(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6'))=k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_21239])).
% 18.90/10.67  tff(c_133, plain, (![A_42, B_43, C_44, D_45]: (k1_relat_1(k4_zfmisc_1(A_42, B_43, C_44, D_45))=k3_zfmisc_1(A_42, B_43, C_44) | D_45='#skF_2' | k3_zfmisc_1(A_42, B_43, C_44)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_122, c_83])).
% 18.90/10.67  tff(c_21269, plain, (k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')=k3_zfmisc_1('#skF_3', '#skF_4', '#skF_9') | '#skF_6'='#skF_2' | k3_zfmisc_1('#skF_3', '#skF_4', '#skF_9')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_21264, c_133])).
% 18.90/10.67  tff(c_21275, plain, (k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')=k3_zfmisc_1('#skF_3', '#skF_4', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_13883, c_21265, c_21269])).
% 18.90/10.67  tff(c_26, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (D_21=A_18 | k3_zfmisc_1(A_18, B_19, C_20)=k1_xboole_0 | k3_zfmisc_1(D_21, E_22, F_23)!=k3_zfmisc_1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 18.90/10.67  tff(c_269, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (D_21=A_18 | k3_zfmisc_1(A_18, B_19, C_20)='#skF_2' | k3_zfmisc_1(D_21, E_22, F_23)!=k3_zfmisc_1(A_18, B_19, C_20))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_26])).
% 18.90/10.67  tff(c_21412, plain, (![D_21, E_22, F_23]: (D_21='#skF_7' | k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')='#skF_2' | k3_zfmisc_1(D_21, E_22, F_23)!=k3_zfmisc_1('#skF_3', '#skF_4', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_21275, c_269])).
% 18.90/10.67  tff(c_21434, plain, (![D_21, E_22, F_23]: (D_21='#skF_7' | k3_zfmisc_1('#skF_3', '#skF_4', '#skF_9')='#skF_2' | k3_zfmisc_1(D_21, E_22, F_23)!=k3_zfmisc_1('#skF_3', '#skF_4', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_21275, c_21412])).
% 18.90/10.67  tff(c_21435, plain, (![D_21, E_22, F_23]: (D_21='#skF_7' | k3_zfmisc_1(D_21, E_22, F_23)!=k3_zfmisc_1('#skF_3', '#skF_4', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_13883, c_21434])).
% 18.90/10.67  tff(c_21792, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_21435])).
% 18.90/10.67  tff(c_21794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_21792])).
% 18.90/10.67  tff(c_21795, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_5288])).
% 18.90/10.67  tff(c_21807, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_21795, c_50])).
% 18.90/10.67  tff(c_21818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_495, c_21807])).
% 18.90/10.67  tff(c_21819, plain, ('#skF_10'='#skF_2'), inference(splitRight, [status(thm)], [c_5178])).
% 18.90/10.67  tff(c_18, plain, (![A_15, C_17, B_16]: (r2_hidden(k2_mcart_1(A_15), C_17) | ~r2_hidden(A_15, k2_zfmisc_1(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.90/10.67  tff(c_690, plain, (![A_112, D_109, B_110, A_111, C_113]: (r2_hidden(k2_mcart_1(A_112), D_109) | ~r2_hidden(A_112, k4_zfmisc_1(A_111, B_110, C_113, D_109)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_18])).
% 18.90/10.67  tff(c_771, plain, (![A_121]: (r2_hidden(k2_mcart_1(A_121), '#skF_10') | ~r2_hidden(A_121, k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_690])).
% 18.90/10.67  tff(c_775, plain, (![A_121]: (~v1_xboole_0('#skF_10') | ~r2_hidden(A_121, k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_771, c_2])).
% 18.90/10.67  tff(c_891, plain, (~v1_xboole_0('#skF_10')), inference(splitLeft, [status(thm)], [c_775])).
% 18.90/10.67  tff(c_21821, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21819, c_891])).
% 18.90/10.67  tff(c_21826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_21821])).
% 18.90/10.67  tff(c_21827, plain, (v1_xboole_0(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_1109])).
% 18.90/10.67  tff(c_21880, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')='#skF_2'), inference(resolution, [status(thm)], [c_21827, c_38])).
% 18.90/10.67  tff(c_21893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_21880])).
% 18.90/10.67  tff(c_21895, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_775])).
% 18.90/10.67  tff(c_21908, plain, ('#skF_10'='#skF_2'), inference(resolution, [status(thm)], [c_21895, c_38])).
% 18.90/10.67  tff(c_21911, plain, (k4_zfmisc_1('#skF_7', '#skF_8', '#skF_9', '#skF_2')=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21908, c_32])).
% 18.90/10.67  tff(c_21914, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_495, c_21911])).
% 18.90/10.67  tff(c_21916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_21914])).
% 18.90/10.67  tff(c_21917, plain, ('#skF_8'!='#skF_4' | '#skF_5'!='#skF_9' | '#skF_10'!='#skF_6'), inference(splitRight, [status(thm)], [c_28])).
% 18.90/10.67  tff(c_21923, plain, ('#skF_10'!='#skF_6'), inference(splitLeft, [status(thm)], [c_21917])).
% 18.90/10.67  tff(c_21918, plain, ('#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 18.90/10.67  tff(c_21969, plain, (k4_zfmisc_1('#skF_3', '#skF_8', '#skF_9', '#skF_10')=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21918, c_32])).
% 18.90/10.67  tff(c_21995, plain, (![A_695, B_696, C_697, D_698]: (k2_zfmisc_1(k3_zfmisc_1(A_695, B_696, C_697), D_698)=k4_zfmisc_1(A_695, B_696, C_697, D_698))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.90/10.67  tff(c_21929, plain, (![A_6, B_7]: (k2_relat_1(k2_zfmisc_1(A_6, B_7))=B_7 | B_7='#skF_2' | A_6='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_37, c_10])).
% 18.90/10.67  tff(c_28660, plain, (![A_1010, B_1011, C_1012, D_1013]: (k2_relat_1(k4_zfmisc_1(A_1010, B_1011, C_1012, D_1013))=D_1013 | D_1013='#skF_2' | k3_zfmisc_1(A_1010, B_1011, C_1012)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_21995, c_21929])).
% 18.90/10.67  tff(c_28705, plain, (k2_relat_1(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_10' | '#skF_10'='#skF_2' | k3_zfmisc_1('#skF_3', '#skF_8', '#skF_9')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_21969, c_28660])).
% 18.90/10.67  tff(c_28715, plain, (k3_zfmisc_1('#skF_3', '#skF_8', '#skF_9')='#skF_2'), inference(splitLeft, [status(thm)], [c_28705])).
% 18.90/10.67  tff(c_23269, plain, (![D_822, B_823, A_824, C_820, A_821]: (r2_hidden(k1_mcart_1(A_824), k3_zfmisc_1(A_821, B_823, C_820)) | ~r2_hidden(A_824, k4_zfmisc_1(A_821, B_823, C_820, D_822)))), inference(superposition, [status(thm), theory('equality')], [c_21995, c_20])).
% 18.90/10.67  tff(c_23342, plain, (![A_833]: (r2_hidden(k1_mcart_1(A_833), k3_zfmisc_1('#skF_3', '#skF_8', '#skF_9')) | ~r2_hidden(A_833, k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_21969, c_23269])).
% 18.90/10.67  tff(c_23352, plain, (![A_833]: (~v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_8', '#skF_9')) | ~r2_hidden(A_833, k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_23342, c_2])).
% 18.90/10.67  tff(c_23777, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_23352])).
% 18.90/10.67  tff(c_28716, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28715, c_23777])).
% 18.90/10.67  tff(c_28720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_28716])).
% 18.90/10.67  tff(c_28721, plain, ('#skF_10'='#skF_2' | k2_relat_1(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_10'), inference(splitRight, [status(thm)], [c_28705])).
% 18.90/10.67  tff(c_28723, plain, (k2_relat_1(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_10'), inference(splitLeft, [status(thm)], [c_28721])).
% 18.90/10.67  tff(c_22009, plain, (![A_695, B_696, C_697, D_698]: (k2_relat_1(k4_zfmisc_1(A_695, B_696, C_697, D_698))=D_698 | D_698='#skF_2' | k3_zfmisc_1(A_695, B_696, C_697)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_21995, c_21929])).
% 18.90/10.67  tff(c_28727, plain, ('#skF_10'='#skF_6' | '#skF_6'='#skF_2' | k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_28723, c_22009])).
% 18.90/10.67  tff(c_28733, plain, ('#skF_6'='#skF_2' | k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_21923, c_28727])).
% 18.90/10.67  tff(c_28736, plain, (k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_28733])).
% 18.90/10.67  tff(c_28901, plain, (![D_14]: (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', D_14)=k2_zfmisc_1('#skF_2', D_14))), inference(superposition, [status(thm), theory('equality')], [c_28736, c_16])).
% 18.90/10.67  tff(c_28927, plain, (![D_14]: (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', D_14)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22069, c_28901])).
% 18.90/10.67  tff(c_28939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28927, c_50])).
% 18.90/10.67  tff(c_28940, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_28733])).
% 18.90/10.67  tff(c_28951, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28940, c_50])).
% 18.90/10.67  tff(c_28962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22419, c_28951])).
% 18.90/10.67  tff(c_28963, plain, ('#skF_10'='#skF_2'), inference(splitRight, [status(thm)], [c_28721])).
% 18.90/10.67  tff(c_22213, plain, (![D_742, A_744, A_741, B_743, C_740]: (r2_hidden(k2_mcart_1(A_744), D_742) | ~r2_hidden(A_744, k4_zfmisc_1(A_741, B_743, C_740, D_742)))), inference(superposition, [status(thm), theory('equality')], [c_21995, c_18])).
% 18.90/10.67  tff(c_22523, plain, (![A_768]: (r2_hidden(k2_mcart_1(A_768), '#skF_10') | ~r2_hidden(A_768, k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_21969, c_22213])).
% 18.90/10.67  tff(c_22527, plain, (![A_768]: (~v1_xboole_0('#skF_10') | ~r2_hidden(A_768, k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_22523, c_2])).
% 18.90/10.67  tff(c_22700, plain, (~v1_xboole_0('#skF_10')), inference(splitLeft, [status(thm)], [c_22527])).
% 18.90/10.67  tff(c_28965, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28963, c_22700])).
% 18.90/10.67  tff(c_28971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_28965])).
% 18.90/10.67  tff(c_28973, plain, (v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_23352])).
% 18.90/10.67  tff(c_29004, plain, (k3_zfmisc_1('#skF_3', '#skF_8', '#skF_9')='#skF_2'), inference(resolution, [status(thm)], [c_28973, c_38])).
% 18.90/10.67  tff(c_29044, plain, (![D_14]: (k4_zfmisc_1('#skF_3', '#skF_8', '#skF_9', D_14)=k2_zfmisc_1('#skF_2', D_14))), inference(superposition, [status(thm), theory('equality')], [c_29004, c_16])).
% 18.90/10.67  tff(c_29056, plain, (![D_14]: (k4_zfmisc_1('#skF_3', '#skF_8', '#skF_9', D_14)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22069, c_29044])).
% 18.90/10.67  tff(c_29058, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_29056, c_21969])).
% 18.90/10.67  tff(c_29060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_29058])).
% 18.90/10.67  tff(c_29062, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_22527])).
% 18.90/10.67  tff(c_29078, plain, ('#skF_10'='#skF_2'), inference(resolution, [status(thm)], [c_29062, c_38])).
% 18.90/10.67  tff(c_29081, plain, (k4_zfmisc_1('#skF_3', '#skF_8', '#skF_9', '#skF_2')=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_29078, c_21969])).
% 18.90/10.67  tff(c_29233, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22419, c_29081])).
% 18.90/10.67  tff(c_29236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_29233])).
% 18.90/10.67  tff(c_29238, plain, ('#skF_10'='#skF_6'), inference(splitRight, [status(thm)], [c_21917])).
% 18.90/10.67  tff(c_29244, plain, (k4_zfmisc_1('#skF_3', '#skF_8', '#skF_9', '#skF_6')=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_29238, c_21918, c_32])).
% 18.90/10.67  tff(c_29315, plain, (![A_1045, B_1046, C_1047, D_1048]: (k2_zfmisc_1(k3_zfmisc_1(A_1045, B_1046, C_1047), D_1048)=k4_zfmisc_1(A_1045, B_1046, C_1047, D_1048))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.90/10.67  tff(c_32105, plain, (![C_1236, D_1234, B_1235, A_1238, A_1237]: (r2_hidden(k1_mcart_1(A_1237), k3_zfmisc_1(A_1238, B_1235, C_1236)) | ~r2_hidden(A_1237, k4_zfmisc_1(A_1238, B_1235, C_1236, D_1234)))), inference(superposition, [status(thm), theory('equality')], [c_29315, c_20])).
% 18.90/10.67  tff(c_32142, plain, (![A_1239]: (r2_hidden(k1_mcart_1(A_1239), k3_zfmisc_1('#skF_3', '#skF_8', '#skF_9')) | ~r2_hidden(A_1239, k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_29244, c_32105])).
% 18.90/10.67  tff(c_32152, plain, (![A_1239]: (~v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_8', '#skF_9')) | ~r2_hidden(A_1239, k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_32142, c_2])).
% 18.90/10.67  tff(c_32998, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_32152])).
% 18.90/10.67  tff(c_33005, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_8'))), inference(resolution, [status(thm)], [c_29925, c_32998])).
% 18.90/10.67  tff(c_33014, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_29359, c_33005])).
% 18.90/10.67  tff(c_29285, plain, (![A_1038, B_1039, C_1040]: (k2_zfmisc_1(k2_zfmisc_1(A_1038, B_1039), C_1040)=k3_zfmisc_1(A_1038, B_1039, C_1040))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.90/10.67  tff(c_29304, plain, (![A_8, B_9, C_10, C_1040]: (k3_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10, C_1040)=k2_zfmisc_1(k3_zfmisc_1(A_8, B_9, C_10), C_1040))), inference(superposition, [status(thm), theory('equality')], [c_14, c_29285])).
% 18.90/10.67  tff(c_30059, plain, (![A_8, B_9, C_10, C_1040]: (k3_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10, C_1040)=k4_zfmisc_1(A_8, B_9, C_10, C_1040))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_29304])).
% 18.90/10.67  tff(c_29741, plain, (![B_16, C_17, C_1110]: (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_1'(k2_zfmisc_1(k2_zfmisc_1(B_16, C_17), C_1110)))), B_16) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_16, C_17), C_1110)))), inference(resolution, [status(thm)], [c_29728, c_20])).
% 18.90/10.67  tff(c_34275, plain, (![B_1311, C_1312, C_1313]: (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_1'(k3_zfmisc_1(B_1311, C_1312, C_1313)))), B_1311) | v1_xboole_0(k3_zfmisc_1(B_1311, C_1312, C_1313)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_29741])).
% 18.90/10.67  tff(c_34359, plain, (![B_1314, C_1315, C_1316]: (~v1_xboole_0(B_1314) | v1_xboole_0(k3_zfmisc_1(B_1314, C_1315, C_1316)))), inference(resolution, [status(thm)], [c_34275, c_2])).
% 18.90/10.67  tff(c_34413, plain, (![A_8, B_9, C_10, C_1040]: (~v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | v1_xboole_0(k4_zfmisc_1(A_8, B_9, C_10, C_1040)))), inference(superposition, [status(thm), theory('equality')], [c_30059, c_34359])).
% 18.90/10.67  tff(c_29301, plain, (![A_15, C_1040, A_1038, B_1039]: (r2_hidden(k2_mcart_1(A_15), C_1040) | ~r2_hidden(A_15, k3_zfmisc_1(A_1038, B_1039, C_1040)))), inference(superposition, [status(thm), theory('equality')], [c_29285, c_18])).
% 18.90/10.67  tff(c_29738, plain, (![A_1038, B_1039, C_1040, C_1110]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1'(k2_zfmisc_1(k3_zfmisc_1(A_1038, B_1039, C_1040), C_1110)))), C_1040) | v1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(A_1038, B_1039, C_1040), C_1110)))), inference(resolution, [status(thm)], [c_29728, c_29301])).
% 18.90/10.67  tff(c_45835, plain, (![A_1583, B_1584, C_1585, C_1586]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1'(k4_zfmisc_1(A_1583, B_1584, C_1585, C_1586)))), C_1585) | v1_xboole_0(k4_zfmisc_1(A_1583, B_1584, C_1585, C_1586)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_29738])).
% 18.90/10.67  tff(c_45926, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1'(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), '#skF_9') | v1_xboole_0(k4_zfmisc_1('#skF_3', '#skF_8', '#skF_9', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_29244, c_45835])).
% 18.90/10.67  tff(c_45943, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1'(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), '#skF_9') | v1_xboole_0(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_29244, c_45926])).
% 18.90/10.67  tff(c_46821, plain, (v1_xboole_0(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_45943])).
% 18.90/10.67  tff(c_46842, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')='#skF_2'), inference(resolution, [status(thm)], [c_46821, c_38])).
% 18.90/10.67  tff(c_46855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_46842])).
% 18.90/10.67  tff(c_46857, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_45943])).
% 18.90/10.67  tff(c_46871, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_34413, c_46857])).
% 18.90/10.67  tff(c_46881, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_29359, c_46871])).
% 18.90/10.67  tff(c_29768, plain, (![B_1109, C_1110]: (~v1_xboole_0(B_1109) | v1_xboole_0(k2_zfmisc_1(B_1109, C_1110)))), inference(resolution, [status(thm)], [c_29728, c_2])).
% 18.90/10.67  tff(c_33013, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_29768, c_33005])).
% 18.90/10.67  tff(c_30060, plain, (![A_1127, B_1128, C_1129, C_1130]: (k3_zfmisc_1(k2_zfmisc_1(A_1127, B_1128), C_1129, C_1130)=k4_zfmisc_1(A_1127, B_1128, C_1129, C_1130))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_29304])).
% 18.90/10.67  tff(c_29362, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (E_22=B_19 | k3_zfmisc_1(A_18, B_19, C_20)='#skF_2' | k3_zfmisc_1(D_21, E_22, F_23)!=k3_zfmisc_1(A_18, B_19, C_20))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_24])).
% 18.90/10.67  tff(c_30092, plain, (![E_22, D_21, A_1127, C_1129, F_23, B_1128, C_1130]: (E_22=C_1129 | k3_zfmisc_1(k2_zfmisc_1(A_1127, B_1128), C_1129, C_1130)='#skF_2' | k4_zfmisc_1(A_1127, B_1128, C_1129, C_1130)!=k3_zfmisc_1(D_21, E_22, F_23))), inference(superposition, [status(thm), theory('equality')], [c_30060, c_29362])).
% 18.90/10.67  tff(c_53656, plain, (![A_1742, F_1740, C_1737, E_1739, B_1736, C_1738, D_1741]: (E_1739=C_1737 | k4_zfmisc_1(A_1742, B_1736, C_1737, C_1738)='#skF_2' | k4_zfmisc_1(A_1742, B_1736, C_1737, C_1738)!=k3_zfmisc_1(D_1741, E_1739, F_1740))), inference(demodulation, [status(thm), theory('equality')], [c_30059, c_30092])).
% 18.90/10.67  tff(c_53803, plain, (![E_1739, D_1741, F_1740]: (E_1739='#skF_9' | k4_zfmisc_1('#skF_3', '#skF_8', '#skF_9', '#skF_6')='#skF_2' | k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k3_zfmisc_1(D_1741, E_1739, F_1740))), inference(superposition, [status(thm), theory('equality')], [c_29244, c_53656])).
% 18.90/10.67  tff(c_53810, plain, (![E_1739, D_1741, F_1740]: (E_1739='#skF_9' | k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')='#skF_2' | k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k3_zfmisc_1(D_1741, E_1739, F_1740))), inference(demodulation, [status(thm), theory('equality')], [c_29244, c_53803])).
% 18.90/10.67  tff(c_53812, plain, (![E_1743, D_1744, F_1745]: (E_1743='#skF_9' | k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k3_zfmisc_1(D_1744, E_1743, F_1745))), inference(negUnitSimplification, [status(thm)], [c_50, c_53810])).
% 18.90/10.67  tff(c_53884, plain, (![C_10, A_8, B_9, C_1040]: (C_10='#skF_9' | k4_zfmisc_1(A_8, B_9, C_10, C_1040)!=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_30059, c_53812])).
% 18.90/10.67  tff(c_54107, plain, ('#skF_5'='#skF_9'), inference(reflexivity, [status(thm), theory('equality')], [c_53884])).
% 18.90/10.67  tff(c_54194, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54107, c_50])).
% 18.90/10.67  tff(c_54193, plain, (k4_zfmisc_1('#skF_3', '#skF_8', '#skF_9', '#skF_6')=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54107, c_29244])).
% 18.90/10.67  tff(c_29487, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (D_21=A_18 | k3_zfmisc_1(A_18, B_19, C_20)='#skF_2' | k3_zfmisc_1(D_21, E_22, F_23)!=k3_zfmisc_1(A_18, B_19, C_20))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_26])).
% 18.90/10.67  tff(c_30073, plain, (![E_22, D_21, A_1127, C_1129, F_23, B_1128, C_1130]: (k2_zfmisc_1(A_1127, B_1128)=D_21 | k3_zfmisc_1(k2_zfmisc_1(A_1127, B_1128), C_1129, C_1130)='#skF_2' | k4_zfmisc_1(A_1127, B_1128, C_1129, C_1130)!=k3_zfmisc_1(D_21, E_22, F_23))), inference(superposition, [status(thm), theory('equality')], [c_30060, c_29487])).
% 18.90/10.67  tff(c_64802, plain, (![B_1951, D_1956, F_1955, A_1957, C_1953, E_1954, C_1952]: (k2_zfmisc_1(A_1957, B_1951)=D_1956 | k4_zfmisc_1(A_1957, B_1951, C_1952, C_1953)='#skF_2' | k4_zfmisc_1(A_1957, B_1951, C_1952, C_1953)!=k3_zfmisc_1(D_1956, E_1954, F_1955))), inference(demodulation, [status(thm), theory('equality')], [c_30059, c_30073])).
% 18.90/10.67  tff(c_64832, plain, (![D_1956, E_1954, F_1955]: (k2_zfmisc_1('#skF_3', '#skF_8')=D_1956 | k4_zfmisc_1('#skF_3', '#skF_8', '#skF_9', '#skF_6')='#skF_2' | k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')!=k3_zfmisc_1(D_1956, E_1954, F_1955))), inference(superposition, [status(thm), theory('equality')], [c_54193, c_64802])).
% 18.90/10.67  tff(c_64977, plain, (![D_1956, E_1954, F_1955]: (k2_zfmisc_1('#skF_3', '#skF_8')=D_1956 | k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')='#skF_2' | k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')!=k3_zfmisc_1(D_1956, E_1954, F_1955))), inference(demodulation, [status(thm), theory('equality')], [c_54193, c_64832])).
% 18.90/10.67  tff(c_67002, plain, (![D_1976, E_1977, F_1978]: (k2_zfmisc_1('#skF_3', '#skF_8')=D_1976 | k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')!=k3_zfmisc_1(D_1976, E_1977, F_1978))), inference(negUnitSimplification, [status(thm)], [c_54194, c_64977])).
% 18.90/10.67  tff(c_67092, plain, (![A_8, B_9, C_10, C_1040]: (k2_zfmisc_1(A_8, B_9)=k2_zfmisc_1('#skF_3', '#skF_8') | k4_zfmisc_1(A_8, B_9, C_10, C_1040)!=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_30059, c_67002])).
% 18.90/10.67  tff(c_94833, plain, (k2_zfmisc_1('#skF_3', '#skF_8')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_67092])).
% 18.90/10.67  tff(c_29272, plain, (![A_6, B_7]: (k2_relat_1(k2_zfmisc_1(A_6, B_7))=B_7 | B_7='#skF_2' | A_6='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_37, c_10])).
% 18.90/10.67  tff(c_95190, plain, (k2_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))='#skF_8' | '#skF_2'='#skF_8' | '#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_94833, c_29272])).
% 18.90/10.67  tff(c_96038, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_95190])).
% 18.90/10.67  tff(c_96190, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96038, c_8])).
% 18.90/10.67  tff(c_96192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33013, c_96190])).
% 18.90/10.67  tff(c_96194, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_95190])).
% 18.90/10.67  tff(c_29237, plain, ('#skF_5'!='#skF_9' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_21917])).
% 18.90/10.67  tff(c_29243, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_29237])).
% 18.90/10.67  tff(c_96193, plain, ('#skF_2'='#skF_8' | k2_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))='#skF_8'), inference(splitRight, [status(thm)], [c_95190])).
% 18.90/10.67  tff(c_96196, plain, (k2_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))='#skF_8'), inference(splitLeft, [status(thm)], [c_96193])).
% 18.90/10.67  tff(c_96200, plain, ('#skF_8'='#skF_4' | '#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_96196, c_29272])).
% 18.90/10.67  tff(c_96206, plain, ('#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_96194, c_29243, c_96200])).
% 18.90/10.67  tff(c_96361, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96206, c_8])).
% 18.90/10.67  tff(c_96363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46881, c_96361])).
% 18.90/10.67  tff(c_96364, plain, ('#skF_2'='#skF_8'), inference(splitRight, [status(thm)], [c_96193])).
% 18.90/10.67  tff(c_96518, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_96364, c_8])).
% 18.90/10.67  tff(c_96520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33014, c_96518])).
% 18.90/10.67  tff(c_96522, plain, (v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_32152])).
% 18.90/10.67  tff(c_96553, plain, (k3_zfmisc_1('#skF_3', '#skF_8', '#skF_9')='#skF_2'), inference(resolution, [status(thm)], [c_96522, c_38])).
% 18.90/10.67  tff(c_96605, plain, (![D_14]: (k4_zfmisc_1('#skF_3', '#skF_8', '#skF_9', D_14)=k2_zfmisc_1('#skF_2', D_14))), inference(superposition, [status(thm), theory('equality')], [c_96553, c_16])).
% 18.90/10.67  tff(c_96620, plain, (![D_14]: (k4_zfmisc_1('#skF_3', '#skF_8', '#skF_9', D_14)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_29791, c_96605])).
% 18.90/10.67  tff(c_96622, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96620, c_29244])).
% 18.90/10.67  tff(c_96624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_96622])).
% 18.90/10.67  tff(c_96625, plain, (![B_1088]: (~v1_xboole_0(B_1088))), inference(splitRight, [status(thm)], [c_29576])).
% 18.90/10.67  tff(c_96631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96625, c_8])).
% 18.90/10.67  tff(c_96633, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_29237])).
% 18.90/10.67  tff(c_96634, plain, (k4_zfmisc_1('#skF_3', '#skF_8', '#skF_9', '#skF_6')=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21918, c_29238, c_32])).
% 18.90/10.67  tff(c_96639, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_96633, c_96634])).
% 18.90/10.67  tff(c_96705, plain, (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96639, c_50])).
% 18.90/10.67  tff(c_96632, plain, ('#skF_5'!='#skF_9'), inference(splitRight, [status(thm)], [c_29237])).
% 18.90/10.67  tff(c_96680, plain, (![A_2306, B_2307, C_2308]: (k2_zfmisc_1(k2_zfmisc_1(A_2306, B_2307), C_2308)=k3_zfmisc_1(A_2306, B_2307, C_2308))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.90/10.67  tff(c_96683, plain, (![A_2306, B_2307, C_2308, C_10]: (k3_zfmisc_1(k2_zfmisc_1(A_2306, B_2307), C_2308, C_10)=k2_zfmisc_1(k3_zfmisc_1(A_2306, B_2307, C_2308), C_10))), inference(superposition, [status(thm), theory('equality')], [c_96680, c_14])).
% 18.90/10.67  tff(c_97759, plain, (![A_2306, B_2307, C_2308, C_10]: (k3_zfmisc_1(k2_zfmisc_1(A_2306, B_2307), C_2308, C_10)=k4_zfmisc_1(A_2306, B_2307, C_2308, C_10))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_96683])).
% 18.90/10.67  tff(c_97760, plain, (![A_2411, B_2412, C_2413, C_2414]: (k3_zfmisc_1(k2_zfmisc_1(A_2411, B_2412), C_2413, C_2414)=k4_zfmisc_1(A_2411, B_2412, C_2413, C_2414))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_96683])).
% 18.90/10.67  tff(c_96860, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (E_22=B_19 | k3_zfmisc_1(A_18, B_19, C_20)='#skF_2' | k3_zfmisc_1(D_21, E_22, F_23)!=k3_zfmisc_1(A_18, B_19, C_20))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_24])).
% 18.90/10.67  tff(c_118203, plain, (![A_2940, C_2937, C_2936, B_2942, C_2939, A_2938, B_2941]: (C_2937=B_2942 | k3_zfmisc_1(A_2938, B_2942, C_2939)='#skF_2' | k4_zfmisc_1(A_2940, B_2941, C_2937, C_2936)!=k3_zfmisc_1(A_2938, B_2942, C_2939))), inference(superposition, [status(thm), theory('equality')], [c_97760, c_96860])).
% 18.90/10.67  tff(c_119289, plain, (![B_2953, A_2954, C_2955]: (B_2953='#skF_5' | k3_zfmisc_1(A_2954, B_2953, C_2955)='#skF_2' | k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')!=k3_zfmisc_1(A_2954, B_2953, C_2955))), inference(superposition, [status(thm), theory('equality')], [c_96639, c_118203])).
% 18.90/10.67  tff(c_119355, plain, (![C_2308, A_2306, B_2307, C_10]: (C_2308='#skF_5' | k3_zfmisc_1(k2_zfmisc_1(A_2306, B_2307), C_2308, C_10)='#skF_2' | k4_zfmisc_1(A_2306, B_2307, C_2308, C_10)!=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_97759, c_119289])).
% 18.90/10.67  tff(c_119369, plain, (![C_2308, A_2306, B_2307, C_10]: (C_2308='#skF_5' | k4_zfmisc_1(A_2306, B_2307, C_2308, C_10)='#skF_2' | k4_zfmisc_1(A_2306, B_2307, C_2308, C_10)!=k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_97759, c_119355])).
% 18.90/10.67  tff(c_120587, plain, ('#skF_5'='#skF_9' | k4_zfmisc_1('#skF_3', '#skF_4', '#skF_9', '#skF_6')='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_119369])).
% 18.90/10.67  tff(c_120589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96705, c_96632, c_120587])).
% 18.90/10.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.90/10.67  
% 18.90/10.67  Inference rules
% 18.90/10.67  ----------------------
% 18.90/10.67  #Ref     : 21
% 18.90/10.67  #Sup     : 31335
% 18.90/10.67  #Fact    : 0
% 18.90/10.67  #Define  : 0
% 18.90/10.67  #Split   : 31
% 18.90/10.67  #Chain   : 0
% 18.90/10.67  #Close   : 0
% 18.90/10.67  
% 18.90/10.67  Ordering : KBO
% 18.90/10.67  
% 18.90/10.67  Simplification rules
% 18.90/10.67  ----------------------
% 18.90/10.67  #Subsume      : 4464
% 18.90/10.67  #Demod        : 24472
% 18.90/10.67  #Tautology    : 21331
% 18.90/10.67  #SimpNegUnit  : 428
% 18.90/10.67  #BackRed      : 630
% 18.90/10.67  
% 18.90/10.67  #Partial instantiations: 0
% 18.90/10.67  #Strategies tried      : 1
% 18.90/10.67  
% 18.90/10.67  Timing (in seconds)
% 18.90/10.67  ----------------------
% 18.90/10.67  Preprocessing        : 0.29
% 18.90/10.67  Parsing              : 0.16
% 18.90/10.67  CNF conversion       : 0.02
% 18.90/10.67  Main loop            : 9.57
% 18.90/10.67  Inferencing          : 2.24
% 18.90/10.67  Reduction            : 2.92
% 18.90/10.67  Demodulation         : 2.12
% 18.90/10.67  BG Simplification    : 0.23
% 18.90/10.67  Subsumption          : 3.69
% 18.90/10.67  Abstraction          : 0.31
% 18.90/10.68  MUC search           : 0.00
% 18.90/10.68  Cooper               : 0.00
% 18.90/10.68  Total                : 9.95
% 18.90/10.68  Index Insertion      : 0.00
% 18.90/10.68  Index Deletion       : 0.00
% 18.90/10.68  Index Matching       : 0.00
% 18.90/10.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
