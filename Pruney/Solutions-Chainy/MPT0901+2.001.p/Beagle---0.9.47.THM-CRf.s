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
% DateTime   : Thu Dec  3 10:09:52 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 279 expanded)
%              Number of leaves         :   32 ( 122 expanded)
%              Depth                    :    9
%              Number of atoms          :  394 (1251 expanded)
%              Number of equality atoms :  336 (1054 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0
          & ~ ! [E] :
                ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
               => ( k8_mcart_1(A,B,C,D,E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                  & k9_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                  & k10_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(E))
                  & k11_mcart_1(A,B,C,D,E) = k2_mcart_1(E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ? [E] :
            ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
            & ! [F] :
                ( m1_subset_1(F,A)
               => ! [G] :
                    ( m1_subset_1(G,B)
                   => ! [H] :
                        ( m1_subset_1(H,C)
                       => ! [I] :
                            ( m1_subset_1(I,D)
                           => E != k4_mcart_1(F,G,H,I) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ? [E] :
            ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
            & ? [F,G,H,I] :
                ( E = k4_mcart_1(F,G,H,I)
                & ~ ( k8_mcart_1(A,B,C,D,E) = F
                    & k9_mcart_1(A,B,C,D,E) = G
                    & k10_mcart_1(A,B,C,D,E) = H
                    & k11_mcart_1(A,B,C,D,E) = I ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    m1_subset_1('#skF_9',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4716,plain,(
    ! [A_1262,C_1264,B_1261,E_1265,D_1263] :
      ( k4_mcart_1('#skF_1'(B_1261,A_1262,D_1263,C_1264,E_1265),'#skF_2'(B_1261,A_1262,D_1263,C_1264,E_1265),'#skF_3'(B_1261,A_1262,D_1263,C_1264,E_1265),'#skF_4'(B_1261,A_1262,D_1263,C_1264,E_1265)) = E_1265
      | ~ m1_subset_1(E_1265,k4_zfmisc_1(A_1262,B_1261,C_1264,D_1263))
      | k1_xboole_0 = D_1263
      | k1_xboole_0 = C_1264
      | k1_xboole_0 = B_1261
      | k1_xboole_0 = A_1262 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3073,plain,(
    ! [A_814,B_815,C_816,D_817] : k4_tarski(k3_mcart_1(A_814,B_815,C_816),D_817) = k4_mcart_1(A_814,B_815,C_816,D_817) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_96,B_97] : k1_mcart_1(k4_tarski(A_96,B_97)) = A_96 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3085,plain,(
    ! [A_814,B_815,C_816,D_817] : k1_mcart_1(k4_mcart_1(A_814,B_815,C_816,D_817)) = k3_mcart_1(A_814,B_815,C_816) ),
    inference(superposition,[status(thm),theory(equality)],[c_3073,c_26])).

tff(c_4792,plain,(
    ! [C_1275,D_1274,E_1271,B_1273,A_1272] :
      ( k3_mcart_1('#skF_1'(B_1273,A_1272,D_1274,C_1275,E_1271),'#skF_2'(B_1273,A_1272,D_1274,C_1275,E_1271),'#skF_3'(B_1273,A_1272,D_1274,C_1275,E_1271)) = k1_mcart_1(E_1271)
      | ~ m1_subset_1(E_1271,k4_zfmisc_1(A_1272,B_1273,C_1275,D_1274))
      | k1_xboole_0 = D_1274
      | k1_xboole_0 = C_1275
      | k1_xboole_0 = B_1273
      | k1_xboole_0 = A_1272 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4716,c_3085])).

tff(c_59,plain,(
    ! [A_103,B_104,C_105] : k4_tarski(k4_tarski(A_103,B_104),C_105) = k3_mcart_1(A_103,B_104,C_105) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_96,B_97] : k2_mcart_1(k4_tarski(A_96,B_97)) = B_97 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_68,plain,(
    ! [A_103,B_104,C_105] : k2_mcart_1(k3_mcart_1(A_103,B_104,C_105)) = C_105 ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_28])).

tff(c_4816,plain,(
    ! [E_1280,D_1278,A_1277,C_1279,B_1276] :
      ( k2_mcart_1(k1_mcart_1(E_1280)) = '#skF_3'(B_1276,A_1277,D_1278,C_1279,E_1280)
      | ~ m1_subset_1(E_1280,k4_zfmisc_1(A_1277,B_1276,C_1279,D_1278))
      | k1_xboole_0 = D_1278
      | k1_xboole_0 = C_1279
      | k1_xboole_0 = B_1276
      | k1_xboole_0 = A_1277 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4792,c_68])).

tff(c_4835,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = '#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_4816])).

tff(c_4842,plain,(
    k2_mcart_1(k1_mcart_1('#skF_9')) = '#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_4835])).

tff(c_3293,plain,(
    ! [B_911,E_915,D_913,A_912,C_914] :
      ( k4_mcart_1('#skF_1'(B_911,A_912,D_913,C_914,E_915),'#skF_2'(B_911,A_912,D_913,C_914,E_915),'#skF_3'(B_911,A_912,D_913,C_914,E_915),'#skF_4'(B_911,A_912,D_913,C_914,E_915)) = E_915
      | ~ m1_subset_1(E_915,k4_zfmisc_1(A_912,B_911,C_914,D_913))
      | k1_xboole_0 = D_913
      | k1_xboole_0 = C_914
      | k1_xboole_0 = B_911
      | k1_xboole_0 = A_912 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3363,plain,(
    ! [E_923,B_922,C_925,A_924,D_921] :
      ( k3_mcart_1('#skF_1'(B_922,A_924,D_921,C_925,E_923),'#skF_2'(B_922,A_924,D_921,C_925,E_923),'#skF_3'(B_922,A_924,D_921,C_925,E_923)) = k1_mcart_1(E_923)
      | ~ m1_subset_1(E_923,k4_zfmisc_1(A_924,B_922,C_925,D_921))
      | k1_xboole_0 = D_921
      | k1_xboole_0 = C_925
      | k1_xboole_0 = B_922
      | k1_xboole_0 = A_924 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3293,c_3085])).

tff(c_71,plain,(
    ! [A_103,B_104,C_105] : k1_mcart_1(k3_mcart_1(A_103,B_104,C_105)) = k4_tarski(A_103,B_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_26])).

tff(c_3422,plain,(
    ! [E_931,C_934,B_935,A_933,D_932] :
      ( k4_tarski('#skF_1'(B_935,A_933,D_932,C_934,E_931),'#skF_2'(B_935,A_933,D_932,C_934,E_931)) = k1_mcart_1(k1_mcart_1(E_931))
      | ~ m1_subset_1(E_931,k4_zfmisc_1(A_933,B_935,C_934,D_932))
      | k1_xboole_0 = D_932
      | k1_xboole_0 = C_934
      | k1_xboole_0 = B_935
      | k1_xboole_0 = A_933 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3363,c_71])).

tff(c_3446,plain,(
    ! [D_936,C_940,E_938,A_937,B_939] :
      ( k2_mcart_1(k1_mcart_1(k1_mcart_1(E_938))) = '#skF_2'(B_939,A_937,D_936,C_940,E_938)
      | ~ m1_subset_1(E_938,k4_zfmisc_1(A_937,B_939,C_940,D_936))
      | k1_xboole_0 = D_936
      | k1_xboole_0 = C_940
      | k1_xboole_0 = B_939
      | k1_xboole_0 = A_937 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3422,c_28])).

tff(c_3460,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = '#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_3446])).

tff(c_3467,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = '#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_3460])).

tff(c_1864,plain,(
    ! [C_569,D_568,A_567,E_570,B_566] :
      ( k4_mcart_1('#skF_1'(B_566,A_567,D_568,C_569,E_570),'#skF_2'(B_566,A_567,D_568,C_569,E_570),'#skF_3'(B_566,A_567,D_568,C_569,E_570),'#skF_4'(B_566,A_567,D_568,C_569,E_570)) = E_570
      | ~ m1_subset_1(E_570,k4_zfmisc_1(A_567,B_566,C_569,D_568))
      | k1_xboole_0 = D_568
      | k1_xboole_0 = C_569
      | k1_xboole_0 = B_566
      | k1_xboole_0 = A_567 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1655,plain,(
    ! [A_478,B_479,C_480,D_481] : k4_tarski(k3_mcart_1(A_478,B_479,C_480),D_481) = k4_mcart_1(A_478,B_479,C_480,D_481) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1664,plain,(
    ! [A_478,B_479,C_480,D_481] : k2_mcart_1(k4_mcart_1(A_478,B_479,C_480,D_481)) = D_481 ),
    inference(superposition,[status(thm),theory(equality)],[c_1655,c_28])).

tff(c_1891,plain,(
    ! [C_575,A_571,D_574,B_572,E_573] :
      ( k2_mcart_1(E_573) = '#skF_4'(B_572,A_571,D_574,C_575,E_573)
      | ~ m1_subset_1(E_573,k4_zfmisc_1(A_571,B_572,C_575,D_574))
      | k1_xboole_0 = D_574
      | k1_xboole_0 = C_575
      | k1_xboole_0 = B_572
      | k1_xboole_0 = A_571 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1864,c_1664])).

tff(c_1910,plain,
    ( k2_mcart_1('#skF_9') = '#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_1891])).

tff(c_1917,plain,(
    k2_mcart_1('#skF_9') = '#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_1910])).

tff(c_336,plain,(
    ! [A_228,C_230,B_227,D_229,E_231] :
      ( k4_mcart_1('#skF_1'(B_227,A_228,D_229,C_230,E_231),'#skF_2'(B_227,A_228,D_229,C_230,E_231),'#skF_3'(B_227,A_228,D_229,C_230,E_231),'#skF_4'(B_227,A_228,D_229,C_230,E_231)) = E_231
      | ~ m1_subset_1(E_231,k4_zfmisc_1(A_228,B_227,C_230,D_229))
      | k1_xboole_0 = D_229
      | k1_xboole_0 = C_230
      | k1_xboole_0 = B_227
      | k1_xboole_0 = A_228 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_108,plain,(
    ! [A_116,B_117,C_118,D_119] : k4_tarski(k3_mcart_1(A_116,B_117,C_118),D_119) = k4_mcart_1(A_116,B_117,C_118,D_119) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    ! [A_116,B_117,C_118,D_119] : k1_mcart_1(k4_mcart_1(A_116,B_117,C_118,D_119)) = k3_mcart_1(A_116,B_117,C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_26])).

tff(c_407,plain,(
    ! [B_237,A_241,E_238,D_240,C_239] :
      ( k3_mcart_1('#skF_1'(B_237,A_241,D_240,C_239,E_238),'#skF_2'(B_237,A_241,D_240,C_239,E_238),'#skF_3'(B_237,A_241,D_240,C_239,E_238)) = k1_mcart_1(E_238)
      | ~ m1_subset_1(E_238,k4_zfmisc_1(A_241,B_237,C_239,D_240))
      | k1_xboole_0 = D_240
      | k1_xboole_0 = C_239
      | k1_xboole_0 = B_237
      | k1_xboole_0 = A_241 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_120])).

tff(c_482,plain,(
    ! [A_258,D_256,E_259,C_257,B_260] :
      ( k4_tarski('#skF_1'(B_260,A_258,D_256,C_257,E_259),'#skF_2'(B_260,A_258,D_256,C_257,E_259)) = k1_mcart_1(k1_mcart_1(E_259))
      | ~ m1_subset_1(E_259,k4_zfmisc_1(A_258,B_260,C_257,D_256))
      | k1_xboole_0 = D_256
      | k1_xboole_0 = C_257
      | k1_xboole_0 = B_260
      | k1_xboole_0 = A_258 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_71])).

tff(c_532,plain,(
    ! [A_268,C_266,B_267,E_270,D_269] :
      ( k1_mcart_1(k1_mcart_1(k1_mcart_1(E_270))) = '#skF_1'(B_267,A_268,D_269,C_266,E_270)
      | ~ m1_subset_1(E_270,k4_zfmisc_1(A_268,B_267,C_266,D_269))
      | k1_xboole_0 = D_269
      | k1_xboole_0 = C_266
      | k1_xboole_0 = B_267
      | k1_xboole_0 = A_268 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_26])).

tff(c_546,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = '#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_532])).

tff(c_553,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = '#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_546])).

tff(c_30,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k2_mcart_1('#skF_9')
    | k2_mcart_1(k1_mcart_1('#skF_9')) != k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')
    | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) != k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')
    | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) != k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_89,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) != k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_554,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != '#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_89])).

tff(c_8,plain,(
    ! [D_15,E_47,C_14,A_12,B_13] :
      ( k4_mcart_1('#skF_1'(B_13,A_12,D_15,C_14,E_47),'#skF_2'(B_13,A_12,D_15,C_14,E_47),'#skF_3'(B_13,A_12,D_15,C_14,E_47),'#skF_4'(B_13,A_12,D_15,C_14,E_47)) = E_47
      | ~ m1_subset_1(E_47,k4_zfmisc_1(A_12,B_13,C_14,D_15))
      | k1_xboole_0 = D_15
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_74,G_93,D_77,B_75,F_92,C_76,H_94,I_95] :
      ( k8_mcart_1(A_74,B_75,C_76,D_77,k4_mcart_1(F_92,G_93,H_94,I_95)) = F_92
      | ~ m1_subset_1(k4_mcart_1(F_92,G_93,H_94,I_95),k4_zfmisc_1(A_74,B_75,C_76,D_77))
      | k1_xboole_0 = D_77
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_846,plain,(
    ! [C_353,D_351,B_356,C_350,D_352,A_355,A_354,E_349,B_348] :
      ( k8_mcart_1(A_355,B_356,C_353,D_352,k4_mcart_1('#skF_1'(B_348,A_354,D_351,C_350,E_349),'#skF_2'(B_348,A_354,D_351,C_350,E_349),'#skF_3'(B_348,A_354,D_351,C_350,E_349),'#skF_4'(B_348,A_354,D_351,C_350,E_349))) = '#skF_1'(B_348,A_354,D_351,C_350,E_349)
      | ~ m1_subset_1(E_349,k4_zfmisc_1(A_355,B_356,C_353,D_352))
      | k1_xboole_0 = D_352
      | k1_xboole_0 = C_353
      | k1_xboole_0 = B_356
      | k1_xboole_0 = A_355
      | ~ m1_subset_1(E_349,k4_zfmisc_1(A_354,B_348,C_350,D_351))
      | k1_xboole_0 = D_351
      | k1_xboole_0 = C_350
      | k1_xboole_0 = B_348
      | k1_xboole_0 = A_354 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_24])).

tff(c_1609,plain,(
    ! [C_465,D_466,B_462,C_467,E_469,B_470,D_468,A_464,A_463] :
      ( k8_mcart_1(A_463,B_470,C_465,D_468,E_469) = '#skF_1'(B_462,A_464,D_466,C_467,E_469)
      | ~ m1_subset_1(E_469,k4_zfmisc_1(A_463,B_470,C_465,D_468))
      | k1_xboole_0 = D_468
      | k1_xboole_0 = C_465
      | k1_xboole_0 = B_470
      | k1_xboole_0 = A_463
      | ~ m1_subset_1(E_469,k4_zfmisc_1(A_464,B_462,C_467,D_466))
      | k1_xboole_0 = D_466
      | k1_xboole_0 = C_467
      | k1_xboole_0 = B_462
      | k1_xboole_0 = A_464
      | ~ m1_subset_1(E_469,k4_zfmisc_1(A_464,B_462,C_467,D_466))
      | k1_xboole_0 = D_466
      | k1_xboole_0 = C_467
      | k1_xboole_0 = B_462
      | k1_xboole_0 = A_464 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_846])).

tff(c_1623,plain,(
    ! [B_462,A_464,D_466,C_467] :
      ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_1'(B_462,A_464,D_466,C_467,'#skF_9')
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_464,B_462,C_467,D_466))
      | k1_xboole_0 = D_466
      | k1_xboole_0 = C_467
      | k1_xboole_0 = B_462
      | k1_xboole_0 = A_464 ) ),
    inference(resolution,[status(thm)],[c_32,c_1609])).

tff(c_1631,plain,(
    ! [B_471,A_472,D_473,C_474] :
      ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_1'(B_471,A_472,D_473,C_474,'#skF_9')
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_472,B_471,C_474,D_473))
      | k1_xboole_0 = D_473
      | k1_xboole_0 = C_474
      | k1_xboole_0 = B_471
      | k1_xboole_0 = A_472 ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_1623])).

tff(c_1634,plain,
    ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_1631])).

tff(c_1638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_554,c_1634])).

tff(c_1639,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) != k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')
    | k2_mcart_1(k1_mcart_1('#skF_9')) != k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')
    | k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k2_mcart_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1654,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k2_mcart_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1639])).

tff(c_1918,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != '#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1917,c_1654])).

tff(c_18,plain,(
    ! [A_74,G_93,D_77,B_75,F_92,C_76,H_94,I_95] :
      ( k11_mcart_1(A_74,B_75,C_76,D_77,k4_mcart_1(F_92,G_93,H_94,I_95)) = I_95
      | ~ m1_subset_1(k4_mcart_1(F_92,G_93,H_94,I_95),k4_zfmisc_1(A_74,B_75,C_76,D_77))
      | k1_xboole_0 = D_77
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2187,plain,(
    ! [D_667,C_666,C_670,D_665,B_669,B_663,A_668,A_662,E_664] :
      ( k11_mcart_1(A_668,B_669,C_666,D_665,k4_mcart_1('#skF_1'(B_663,A_662,D_667,C_670,E_664),'#skF_2'(B_663,A_662,D_667,C_670,E_664),'#skF_3'(B_663,A_662,D_667,C_670,E_664),'#skF_4'(B_663,A_662,D_667,C_670,E_664))) = '#skF_4'(B_663,A_662,D_667,C_670,E_664)
      | ~ m1_subset_1(E_664,k4_zfmisc_1(A_668,B_669,C_666,D_665))
      | k1_xboole_0 = D_665
      | k1_xboole_0 = C_666
      | k1_xboole_0 = B_669
      | k1_xboole_0 = A_668
      | ~ m1_subset_1(E_664,k4_zfmisc_1(A_662,B_663,C_670,D_667))
      | k1_xboole_0 = D_667
      | k1_xboole_0 = C_670
      | k1_xboole_0 = B_663
      | k1_xboole_0 = A_662 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1864,c_18])).

tff(c_3037,plain,(
    ! [C_807,A_805,D_803,E_808,C_801,D_806,B_809,B_802,A_804] :
      ( k11_mcart_1(A_805,B_809,C_801,D_803,E_808) = '#skF_4'(B_802,A_804,D_806,C_807,E_808)
      | ~ m1_subset_1(E_808,k4_zfmisc_1(A_805,B_809,C_801,D_803))
      | k1_xboole_0 = D_803
      | k1_xboole_0 = C_801
      | k1_xboole_0 = B_809
      | k1_xboole_0 = A_805
      | ~ m1_subset_1(E_808,k4_zfmisc_1(A_804,B_802,C_807,D_806))
      | k1_xboole_0 = D_806
      | k1_xboole_0 = C_807
      | k1_xboole_0 = B_802
      | k1_xboole_0 = A_804
      | ~ m1_subset_1(E_808,k4_zfmisc_1(A_804,B_802,C_807,D_806))
      | k1_xboole_0 = D_806
      | k1_xboole_0 = C_807
      | k1_xboole_0 = B_802
      | k1_xboole_0 = A_804 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2187])).

tff(c_3051,plain,(
    ! [B_802,A_804,D_806,C_807] :
      ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_4'(B_802,A_804,D_806,C_807,'#skF_9')
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_804,B_802,C_807,D_806))
      | k1_xboole_0 = D_806
      | k1_xboole_0 = C_807
      | k1_xboole_0 = B_802
      | k1_xboole_0 = A_804 ) ),
    inference(resolution,[status(thm)],[c_32,c_3037])).

tff(c_3059,plain,(
    ! [B_810,A_811,D_812,C_813] :
      ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_4'(B_810,A_811,D_812,C_813,'#skF_9')
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_811,B_810,C_813,D_812))
      | k1_xboole_0 = D_812
      | k1_xboole_0 = C_813
      | k1_xboole_0 = B_810
      | k1_xboole_0 = A_811 ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_3051])).

tff(c_3062,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_4'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_3059])).

tff(c_3066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_1918,c_3062])).

tff(c_3067,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) != k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')
    | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) != k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_1639])).

tff(c_3091,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) != k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3067])).

tff(c_3468,plain,(
    k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != '#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3467,c_3091])).

tff(c_22,plain,(
    ! [A_74,G_93,D_77,B_75,F_92,C_76,H_94,I_95] :
      ( k9_mcart_1(A_74,B_75,C_76,D_77,k4_mcart_1(F_92,G_93,H_94,I_95)) = G_93
      | ~ m1_subset_1(k4_mcart_1(F_92,G_93,H_94,I_95),k4_zfmisc_1(A_74,B_75,C_76,D_77))
      | k1_xboole_0 = D_77
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3612,plain,(
    ! [D_1003,D_999,B_1000,E_1001,C_1005,A_1002,B_1007,C_1004,A_1006] :
      ( k9_mcart_1(A_1006,B_1007,C_1004,D_1003,k4_mcart_1('#skF_1'(B_1000,A_1002,D_999,C_1005,E_1001),'#skF_2'(B_1000,A_1002,D_999,C_1005,E_1001),'#skF_3'(B_1000,A_1002,D_999,C_1005,E_1001),'#skF_4'(B_1000,A_1002,D_999,C_1005,E_1001))) = '#skF_2'(B_1000,A_1002,D_999,C_1005,E_1001)
      | ~ m1_subset_1(E_1001,k4_zfmisc_1(A_1006,B_1007,C_1004,D_1003))
      | k1_xboole_0 = D_1003
      | k1_xboole_0 = C_1004
      | k1_xboole_0 = B_1007
      | k1_xboole_0 = A_1006
      | ~ m1_subset_1(E_1001,k4_zfmisc_1(A_1002,B_1000,C_1005,D_999))
      | k1_xboole_0 = D_999
      | k1_xboole_0 = C_1005
      | k1_xboole_0 = B_1000
      | k1_xboole_0 = A_1002 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3293,c_22])).

tff(c_4462,plain,(
    ! [B_1137,A_1138,D_1139,C_1142,D_1143,A_1141,E_1145,B_1140,C_1144] :
      ( k9_mcart_1(A_1138,B_1140,C_1142,D_1139,E_1145) = '#skF_2'(B_1137,A_1141,D_1143,C_1144,E_1145)
      | ~ m1_subset_1(E_1145,k4_zfmisc_1(A_1138,B_1140,C_1142,D_1139))
      | k1_xboole_0 = D_1139
      | k1_xboole_0 = C_1142
      | k1_xboole_0 = B_1140
      | k1_xboole_0 = A_1138
      | ~ m1_subset_1(E_1145,k4_zfmisc_1(A_1141,B_1137,C_1144,D_1143))
      | k1_xboole_0 = D_1143
      | k1_xboole_0 = C_1144
      | k1_xboole_0 = B_1137
      | k1_xboole_0 = A_1141
      | ~ m1_subset_1(E_1145,k4_zfmisc_1(A_1141,B_1137,C_1144,D_1143))
      | k1_xboole_0 = D_1143
      | k1_xboole_0 = C_1144
      | k1_xboole_0 = B_1137
      | k1_xboole_0 = A_1141 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3612])).

tff(c_4476,plain,(
    ! [B_1137,A_1141,D_1143,C_1144] :
      ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_2'(B_1137,A_1141,D_1143,C_1144,'#skF_9')
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_1141,B_1137,C_1144,D_1143))
      | k1_xboole_0 = D_1143
      | k1_xboole_0 = C_1144
      | k1_xboole_0 = B_1137
      | k1_xboole_0 = A_1141 ) ),
    inference(resolution,[status(thm)],[c_32,c_4462])).

tff(c_4484,plain,(
    ! [B_1146,A_1147,D_1148,C_1149] :
      ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_2'(B_1146,A_1147,D_1148,C_1149,'#skF_9')
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_1147,B_1146,C_1149,D_1148))
      | k1_xboole_0 = D_1148
      | k1_xboole_0 = C_1149
      | k1_xboole_0 = B_1146
      | k1_xboole_0 = A_1147 ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_4476])).

tff(c_4487,plain,
    ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_2'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_4484])).

tff(c_4491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_3468,c_4487])).

tff(c_4492,plain,(
    k2_mcart_1(k1_mcart_1('#skF_9')) != k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_3067])).

tff(c_4843,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != '#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4842,c_4492])).

tff(c_20,plain,(
    ! [A_74,G_93,D_77,B_75,F_92,C_76,H_94,I_95] :
      ( k10_mcart_1(A_74,B_75,C_76,D_77,k4_mcart_1(F_92,G_93,H_94,I_95)) = H_94
      | ~ m1_subset_1(k4_mcart_1(F_92,G_93,H_94,I_95),k4_zfmisc_1(A_74,B_75,C_76,D_77))
      | k1_xboole_0 = D_77
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_75
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5294,plain,(
    ! [C_1396,B_1398,A_1397,D_1393,D_1394,E_1390,A_1391,C_1395,B_1392] :
      ( k10_mcart_1(A_1397,B_1398,C_1395,D_1394,k4_mcart_1('#skF_1'(B_1392,A_1391,D_1393,C_1396,E_1390),'#skF_2'(B_1392,A_1391,D_1393,C_1396,E_1390),'#skF_3'(B_1392,A_1391,D_1393,C_1396,E_1390),'#skF_4'(B_1392,A_1391,D_1393,C_1396,E_1390))) = '#skF_3'(B_1392,A_1391,D_1393,C_1396,E_1390)
      | ~ m1_subset_1(E_1390,k4_zfmisc_1(A_1397,B_1398,C_1395,D_1394))
      | k1_xboole_0 = D_1394
      | k1_xboole_0 = C_1395
      | k1_xboole_0 = B_1398
      | k1_xboole_0 = A_1397
      | ~ m1_subset_1(E_1390,k4_zfmisc_1(A_1391,B_1392,C_1396,D_1393))
      | k1_xboole_0 = D_1393
      | k1_xboole_0 = C_1396
      | k1_xboole_0 = B_1392
      | k1_xboole_0 = A_1391 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4716,c_20])).

tff(c_6503,plain,(
    ! [B_1571,A_1574,C_1572,A_1573,E_1579,D_1576,B_1575,D_1577,C_1578] :
      ( k10_mcart_1(A_1573,B_1575,C_1572,D_1576,E_1579) = '#skF_3'(B_1571,A_1574,D_1577,C_1578,E_1579)
      | ~ m1_subset_1(E_1579,k4_zfmisc_1(A_1573,B_1575,C_1572,D_1576))
      | k1_xboole_0 = D_1576
      | k1_xboole_0 = C_1572
      | k1_xboole_0 = B_1575
      | k1_xboole_0 = A_1573
      | ~ m1_subset_1(E_1579,k4_zfmisc_1(A_1574,B_1571,C_1578,D_1577))
      | k1_xboole_0 = D_1577
      | k1_xboole_0 = C_1578
      | k1_xboole_0 = B_1571
      | k1_xboole_0 = A_1574
      | ~ m1_subset_1(E_1579,k4_zfmisc_1(A_1574,B_1571,C_1578,D_1577))
      | k1_xboole_0 = D_1577
      | k1_xboole_0 = C_1578
      | k1_xboole_0 = B_1571
      | k1_xboole_0 = A_1574 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_5294])).

tff(c_6517,plain,(
    ! [B_1571,A_1574,D_1577,C_1578] :
      ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_3'(B_1571,A_1574,D_1577,C_1578,'#skF_9')
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_1574,B_1571,C_1578,D_1577))
      | k1_xboole_0 = D_1577
      | k1_xboole_0 = C_1578
      | k1_xboole_0 = B_1571
      | k1_xboole_0 = A_1574 ) ),
    inference(resolution,[status(thm)],[c_32,c_6503])).

tff(c_6525,plain,(
    ! [B_1580,A_1581,D_1582,C_1583] :
      ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_3'(B_1580,A_1581,D_1582,C_1583,'#skF_9')
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_1581,B_1580,C_1583,D_1582))
      | k1_xboole_0 = D_1582
      | k1_xboole_0 = C_1583
      | k1_xboole_0 = B_1580
      | k1_xboole_0 = A_1581 ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_6517])).

tff(c_6528,plain,
    ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_3'('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_6525])).

tff(c_6532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_34,c_4843,c_6528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.65/2.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.89/2.83  
% 7.89/2.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.89/2.84  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 7.89/2.84  
% 7.89/2.84  %Foreground sorts:
% 7.89/2.84  
% 7.89/2.84  
% 7.89/2.84  %Background operators:
% 7.89/2.84  
% 7.89/2.84  
% 7.89/2.84  %Foreground operators:
% 7.89/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.89/2.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 7.89/2.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.89/2.84  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 7.89/2.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.89/2.84  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 7.89/2.84  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.89/2.84  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 7.89/2.84  tff('#skF_7', type, '#skF_7': $i).
% 7.89/2.84  tff('#skF_5', type, '#skF_5': $i).
% 7.89/2.84  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 7.89/2.84  tff('#skF_6', type, '#skF_6': $i).
% 7.89/2.84  tff('#skF_9', type, '#skF_9': $i).
% 7.89/2.84  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.89/2.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 7.89/2.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 7.89/2.84  tff('#skF_8', type, '#skF_8': $i).
% 7.89/2.84  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 7.89/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.89/2.84  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.89/2.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.89/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.89/2.84  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.89/2.84  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 7.89/2.84  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 7.89/2.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.89/2.84  
% 7.89/2.86  tff(f_120, negated_conjecture, ~(![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 7.89/2.86  tff(f_62, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 7.89/2.86  tff(f_29, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 7.89/2.86  tff(f_94, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 7.89/2.86  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 7.89/2.86  tff(f_90, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_mcart_1)).
% 7.89/2.86  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.89/2.86  tff(c_38, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.89/2.86  tff(c_36, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.89/2.86  tff(c_34, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.89/2.86  tff(c_32, plain, (m1_subset_1('#skF_9', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.89/2.86  tff(c_4716, plain, (![A_1262, C_1264, B_1261, E_1265, D_1263]: (k4_mcart_1('#skF_1'(B_1261, A_1262, D_1263, C_1264, E_1265), '#skF_2'(B_1261, A_1262, D_1263, C_1264, E_1265), '#skF_3'(B_1261, A_1262, D_1263, C_1264, E_1265), '#skF_4'(B_1261, A_1262, D_1263, C_1264, E_1265))=E_1265 | ~m1_subset_1(E_1265, k4_zfmisc_1(A_1262, B_1261, C_1264, D_1263)) | k1_xboole_0=D_1263 | k1_xboole_0=C_1264 | k1_xboole_0=B_1261 | k1_xboole_0=A_1262)), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.89/2.86  tff(c_3073, plain, (![A_814, B_815, C_816, D_817]: (k4_tarski(k3_mcart_1(A_814, B_815, C_816), D_817)=k4_mcart_1(A_814, B_815, C_816, D_817))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.89/2.86  tff(c_26, plain, (![A_96, B_97]: (k1_mcart_1(k4_tarski(A_96, B_97))=A_96)), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.89/2.86  tff(c_3085, plain, (![A_814, B_815, C_816, D_817]: (k1_mcart_1(k4_mcart_1(A_814, B_815, C_816, D_817))=k3_mcart_1(A_814, B_815, C_816))), inference(superposition, [status(thm), theory('equality')], [c_3073, c_26])).
% 7.89/2.86  tff(c_4792, plain, (![C_1275, D_1274, E_1271, B_1273, A_1272]: (k3_mcart_1('#skF_1'(B_1273, A_1272, D_1274, C_1275, E_1271), '#skF_2'(B_1273, A_1272, D_1274, C_1275, E_1271), '#skF_3'(B_1273, A_1272, D_1274, C_1275, E_1271))=k1_mcart_1(E_1271) | ~m1_subset_1(E_1271, k4_zfmisc_1(A_1272, B_1273, C_1275, D_1274)) | k1_xboole_0=D_1274 | k1_xboole_0=C_1275 | k1_xboole_0=B_1273 | k1_xboole_0=A_1272)), inference(superposition, [status(thm), theory('equality')], [c_4716, c_3085])).
% 7.89/2.86  tff(c_59, plain, (![A_103, B_104, C_105]: (k4_tarski(k4_tarski(A_103, B_104), C_105)=k3_mcart_1(A_103, B_104, C_105))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.89/2.86  tff(c_28, plain, (![A_96, B_97]: (k2_mcart_1(k4_tarski(A_96, B_97))=B_97)), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.89/2.86  tff(c_68, plain, (![A_103, B_104, C_105]: (k2_mcart_1(k3_mcart_1(A_103, B_104, C_105))=C_105)), inference(superposition, [status(thm), theory('equality')], [c_59, c_28])).
% 7.89/2.86  tff(c_4816, plain, (![E_1280, D_1278, A_1277, C_1279, B_1276]: (k2_mcart_1(k1_mcart_1(E_1280))='#skF_3'(B_1276, A_1277, D_1278, C_1279, E_1280) | ~m1_subset_1(E_1280, k4_zfmisc_1(A_1277, B_1276, C_1279, D_1278)) | k1_xboole_0=D_1278 | k1_xboole_0=C_1279 | k1_xboole_0=B_1276 | k1_xboole_0=A_1277)), inference(superposition, [status(thm), theory('equality')], [c_4792, c_68])).
% 7.89/2.86  tff(c_4835, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))='#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_32, c_4816])).
% 7.89/2.86  tff(c_4842, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))='#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_4835])).
% 7.89/2.86  tff(c_3293, plain, (![B_911, E_915, D_913, A_912, C_914]: (k4_mcart_1('#skF_1'(B_911, A_912, D_913, C_914, E_915), '#skF_2'(B_911, A_912, D_913, C_914, E_915), '#skF_3'(B_911, A_912, D_913, C_914, E_915), '#skF_4'(B_911, A_912, D_913, C_914, E_915))=E_915 | ~m1_subset_1(E_915, k4_zfmisc_1(A_912, B_911, C_914, D_913)) | k1_xboole_0=D_913 | k1_xboole_0=C_914 | k1_xboole_0=B_911 | k1_xboole_0=A_912)), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.89/2.86  tff(c_3363, plain, (![E_923, B_922, C_925, A_924, D_921]: (k3_mcart_1('#skF_1'(B_922, A_924, D_921, C_925, E_923), '#skF_2'(B_922, A_924, D_921, C_925, E_923), '#skF_3'(B_922, A_924, D_921, C_925, E_923))=k1_mcart_1(E_923) | ~m1_subset_1(E_923, k4_zfmisc_1(A_924, B_922, C_925, D_921)) | k1_xboole_0=D_921 | k1_xboole_0=C_925 | k1_xboole_0=B_922 | k1_xboole_0=A_924)), inference(superposition, [status(thm), theory('equality')], [c_3293, c_3085])).
% 7.89/2.86  tff(c_71, plain, (![A_103, B_104, C_105]: (k1_mcart_1(k3_mcart_1(A_103, B_104, C_105))=k4_tarski(A_103, B_104))), inference(superposition, [status(thm), theory('equality')], [c_59, c_26])).
% 7.89/2.86  tff(c_3422, plain, (![E_931, C_934, B_935, A_933, D_932]: (k4_tarski('#skF_1'(B_935, A_933, D_932, C_934, E_931), '#skF_2'(B_935, A_933, D_932, C_934, E_931))=k1_mcart_1(k1_mcart_1(E_931)) | ~m1_subset_1(E_931, k4_zfmisc_1(A_933, B_935, C_934, D_932)) | k1_xboole_0=D_932 | k1_xboole_0=C_934 | k1_xboole_0=B_935 | k1_xboole_0=A_933)), inference(superposition, [status(thm), theory('equality')], [c_3363, c_71])).
% 7.89/2.86  tff(c_3446, plain, (![D_936, C_940, E_938, A_937, B_939]: (k2_mcart_1(k1_mcart_1(k1_mcart_1(E_938)))='#skF_2'(B_939, A_937, D_936, C_940, E_938) | ~m1_subset_1(E_938, k4_zfmisc_1(A_937, B_939, C_940, D_936)) | k1_xboole_0=D_936 | k1_xboole_0=C_940 | k1_xboole_0=B_939 | k1_xboole_0=A_937)), inference(superposition, [status(thm), theory('equality')], [c_3422, c_28])).
% 7.89/2.86  tff(c_3460, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))='#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_32, c_3446])).
% 7.89/2.86  tff(c_3467, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))='#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_3460])).
% 7.89/2.86  tff(c_1864, plain, (![C_569, D_568, A_567, E_570, B_566]: (k4_mcart_1('#skF_1'(B_566, A_567, D_568, C_569, E_570), '#skF_2'(B_566, A_567, D_568, C_569, E_570), '#skF_3'(B_566, A_567, D_568, C_569, E_570), '#skF_4'(B_566, A_567, D_568, C_569, E_570))=E_570 | ~m1_subset_1(E_570, k4_zfmisc_1(A_567, B_566, C_569, D_568)) | k1_xboole_0=D_568 | k1_xboole_0=C_569 | k1_xboole_0=B_566 | k1_xboole_0=A_567)), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.89/2.86  tff(c_1655, plain, (![A_478, B_479, C_480, D_481]: (k4_tarski(k3_mcart_1(A_478, B_479, C_480), D_481)=k4_mcart_1(A_478, B_479, C_480, D_481))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.89/2.86  tff(c_1664, plain, (![A_478, B_479, C_480, D_481]: (k2_mcart_1(k4_mcart_1(A_478, B_479, C_480, D_481))=D_481)), inference(superposition, [status(thm), theory('equality')], [c_1655, c_28])).
% 7.89/2.86  tff(c_1891, plain, (![C_575, A_571, D_574, B_572, E_573]: (k2_mcart_1(E_573)='#skF_4'(B_572, A_571, D_574, C_575, E_573) | ~m1_subset_1(E_573, k4_zfmisc_1(A_571, B_572, C_575, D_574)) | k1_xboole_0=D_574 | k1_xboole_0=C_575 | k1_xboole_0=B_572 | k1_xboole_0=A_571)), inference(superposition, [status(thm), theory('equality')], [c_1864, c_1664])).
% 7.89/2.86  tff(c_1910, plain, (k2_mcart_1('#skF_9')='#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_32, c_1891])).
% 7.89/2.86  tff(c_1917, plain, (k2_mcart_1('#skF_9')='#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_1910])).
% 7.89/2.86  tff(c_336, plain, (![A_228, C_230, B_227, D_229, E_231]: (k4_mcart_1('#skF_1'(B_227, A_228, D_229, C_230, E_231), '#skF_2'(B_227, A_228, D_229, C_230, E_231), '#skF_3'(B_227, A_228, D_229, C_230, E_231), '#skF_4'(B_227, A_228, D_229, C_230, E_231))=E_231 | ~m1_subset_1(E_231, k4_zfmisc_1(A_228, B_227, C_230, D_229)) | k1_xboole_0=D_229 | k1_xboole_0=C_230 | k1_xboole_0=B_227 | k1_xboole_0=A_228)), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.89/2.86  tff(c_108, plain, (![A_116, B_117, C_118, D_119]: (k4_tarski(k3_mcart_1(A_116, B_117, C_118), D_119)=k4_mcart_1(A_116, B_117, C_118, D_119))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.89/2.86  tff(c_120, plain, (![A_116, B_117, C_118, D_119]: (k1_mcart_1(k4_mcart_1(A_116, B_117, C_118, D_119))=k3_mcart_1(A_116, B_117, C_118))), inference(superposition, [status(thm), theory('equality')], [c_108, c_26])).
% 7.89/2.86  tff(c_407, plain, (![B_237, A_241, E_238, D_240, C_239]: (k3_mcart_1('#skF_1'(B_237, A_241, D_240, C_239, E_238), '#skF_2'(B_237, A_241, D_240, C_239, E_238), '#skF_3'(B_237, A_241, D_240, C_239, E_238))=k1_mcart_1(E_238) | ~m1_subset_1(E_238, k4_zfmisc_1(A_241, B_237, C_239, D_240)) | k1_xboole_0=D_240 | k1_xboole_0=C_239 | k1_xboole_0=B_237 | k1_xboole_0=A_241)), inference(superposition, [status(thm), theory('equality')], [c_336, c_120])).
% 7.89/2.86  tff(c_482, plain, (![A_258, D_256, E_259, C_257, B_260]: (k4_tarski('#skF_1'(B_260, A_258, D_256, C_257, E_259), '#skF_2'(B_260, A_258, D_256, C_257, E_259))=k1_mcart_1(k1_mcart_1(E_259)) | ~m1_subset_1(E_259, k4_zfmisc_1(A_258, B_260, C_257, D_256)) | k1_xboole_0=D_256 | k1_xboole_0=C_257 | k1_xboole_0=B_260 | k1_xboole_0=A_258)), inference(superposition, [status(thm), theory('equality')], [c_407, c_71])).
% 7.89/2.86  tff(c_532, plain, (![A_268, C_266, B_267, E_270, D_269]: (k1_mcart_1(k1_mcart_1(k1_mcart_1(E_270)))='#skF_1'(B_267, A_268, D_269, C_266, E_270) | ~m1_subset_1(E_270, k4_zfmisc_1(A_268, B_267, C_266, D_269)) | k1_xboole_0=D_269 | k1_xboole_0=C_266 | k1_xboole_0=B_267 | k1_xboole_0=A_268)), inference(superposition, [status(thm), theory('equality')], [c_482, c_26])).
% 7.89/2.86  tff(c_546, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))='#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_32, c_532])).
% 7.89/2.86  tff(c_553, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))='#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_546])).
% 7.89/2.86  tff(c_30, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k2_mcart_1('#skF_9') | k2_mcart_1(k1_mcart_1('#skF_9'))!=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9') | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))!=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9') | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))!=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.89/2.86  tff(c_89, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))!=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_30])).
% 7.89/2.86  tff(c_554, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!='#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_553, c_89])).
% 7.89/2.86  tff(c_8, plain, (![D_15, E_47, C_14, A_12, B_13]: (k4_mcart_1('#skF_1'(B_13, A_12, D_15, C_14, E_47), '#skF_2'(B_13, A_12, D_15, C_14, E_47), '#skF_3'(B_13, A_12, D_15, C_14, E_47), '#skF_4'(B_13, A_12, D_15, C_14, E_47))=E_47 | ~m1_subset_1(E_47, k4_zfmisc_1(A_12, B_13, C_14, D_15)) | k1_xboole_0=D_15 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.89/2.86  tff(c_24, plain, (![A_74, G_93, D_77, B_75, F_92, C_76, H_94, I_95]: (k8_mcart_1(A_74, B_75, C_76, D_77, k4_mcart_1(F_92, G_93, H_94, I_95))=F_92 | ~m1_subset_1(k4_mcart_1(F_92, G_93, H_94, I_95), k4_zfmisc_1(A_74, B_75, C_76, D_77)) | k1_xboole_0=D_77 | k1_xboole_0=C_76 | k1_xboole_0=B_75 | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.89/2.86  tff(c_846, plain, (![C_353, D_351, B_356, C_350, D_352, A_355, A_354, E_349, B_348]: (k8_mcart_1(A_355, B_356, C_353, D_352, k4_mcart_1('#skF_1'(B_348, A_354, D_351, C_350, E_349), '#skF_2'(B_348, A_354, D_351, C_350, E_349), '#skF_3'(B_348, A_354, D_351, C_350, E_349), '#skF_4'(B_348, A_354, D_351, C_350, E_349)))='#skF_1'(B_348, A_354, D_351, C_350, E_349) | ~m1_subset_1(E_349, k4_zfmisc_1(A_355, B_356, C_353, D_352)) | k1_xboole_0=D_352 | k1_xboole_0=C_353 | k1_xboole_0=B_356 | k1_xboole_0=A_355 | ~m1_subset_1(E_349, k4_zfmisc_1(A_354, B_348, C_350, D_351)) | k1_xboole_0=D_351 | k1_xboole_0=C_350 | k1_xboole_0=B_348 | k1_xboole_0=A_354)), inference(superposition, [status(thm), theory('equality')], [c_336, c_24])).
% 7.89/2.86  tff(c_1609, plain, (![C_465, D_466, B_462, C_467, E_469, B_470, D_468, A_464, A_463]: (k8_mcart_1(A_463, B_470, C_465, D_468, E_469)='#skF_1'(B_462, A_464, D_466, C_467, E_469) | ~m1_subset_1(E_469, k4_zfmisc_1(A_463, B_470, C_465, D_468)) | k1_xboole_0=D_468 | k1_xboole_0=C_465 | k1_xboole_0=B_470 | k1_xboole_0=A_463 | ~m1_subset_1(E_469, k4_zfmisc_1(A_464, B_462, C_467, D_466)) | k1_xboole_0=D_466 | k1_xboole_0=C_467 | k1_xboole_0=B_462 | k1_xboole_0=A_464 | ~m1_subset_1(E_469, k4_zfmisc_1(A_464, B_462, C_467, D_466)) | k1_xboole_0=D_466 | k1_xboole_0=C_467 | k1_xboole_0=B_462 | k1_xboole_0=A_464)), inference(superposition, [status(thm), theory('equality')], [c_8, c_846])).
% 7.89/2.86  tff(c_1623, plain, (![B_462, A_464, D_466, C_467]: (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_1'(B_462, A_464, D_466, C_467, '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_464, B_462, C_467, D_466)) | k1_xboole_0=D_466 | k1_xboole_0=C_467 | k1_xboole_0=B_462 | k1_xboole_0=A_464)), inference(resolution, [status(thm)], [c_32, c_1609])).
% 7.89/2.86  tff(c_1631, plain, (![B_471, A_472, D_473, C_474]: (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_1'(B_471, A_472, D_473, C_474, '#skF_9') | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_472, B_471, C_474, D_473)) | k1_xboole_0=D_473 | k1_xboole_0=C_474 | k1_xboole_0=B_471 | k1_xboole_0=A_472)), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_1623])).
% 7.89/2.86  tff(c_1634, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_32, c_1631])).
% 7.89/2.86  tff(c_1638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_554, c_1634])).
% 7.89/2.86  tff(c_1639, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))!=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9') | k2_mcart_1(k1_mcart_1('#skF_9'))!=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9') | k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k2_mcart_1('#skF_9')), inference(splitRight, [status(thm)], [c_30])).
% 7.89/2.86  tff(c_1654, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k2_mcart_1('#skF_9')), inference(splitLeft, [status(thm)], [c_1639])).
% 7.89/2.86  tff(c_1918, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!='#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1917, c_1654])).
% 7.89/2.86  tff(c_18, plain, (![A_74, G_93, D_77, B_75, F_92, C_76, H_94, I_95]: (k11_mcart_1(A_74, B_75, C_76, D_77, k4_mcart_1(F_92, G_93, H_94, I_95))=I_95 | ~m1_subset_1(k4_mcart_1(F_92, G_93, H_94, I_95), k4_zfmisc_1(A_74, B_75, C_76, D_77)) | k1_xboole_0=D_77 | k1_xboole_0=C_76 | k1_xboole_0=B_75 | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.89/2.86  tff(c_2187, plain, (![D_667, C_666, C_670, D_665, B_669, B_663, A_668, A_662, E_664]: (k11_mcart_1(A_668, B_669, C_666, D_665, k4_mcart_1('#skF_1'(B_663, A_662, D_667, C_670, E_664), '#skF_2'(B_663, A_662, D_667, C_670, E_664), '#skF_3'(B_663, A_662, D_667, C_670, E_664), '#skF_4'(B_663, A_662, D_667, C_670, E_664)))='#skF_4'(B_663, A_662, D_667, C_670, E_664) | ~m1_subset_1(E_664, k4_zfmisc_1(A_668, B_669, C_666, D_665)) | k1_xboole_0=D_665 | k1_xboole_0=C_666 | k1_xboole_0=B_669 | k1_xboole_0=A_668 | ~m1_subset_1(E_664, k4_zfmisc_1(A_662, B_663, C_670, D_667)) | k1_xboole_0=D_667 | k1_xboole_0=C_670 | k1_xboole_0=B_663 | k1_xboole_0=A_662)), inference(superposition, [status(thm), theory('equality')], [c_1864, c_18])).
% 7.89/2.86  tff(c_3037, plain, (![C_807, A_805, D_803, E_808, C_801, D_806, B_809, B_802, A_804]: (k11_mcart_1(A_805, B_809, C_801, D_803, E_808)='#skF_4'(B_802, A_804, D_806, C_807, E_808) | ~m1_subset_1(E_808, k4_zfmisc_1(A_805, B_809, C_801, D_803)) | k1_xboole_0=D_803 | k1_xboole_0=C_801 | k1_xboole_0=B_809 | k1_xboole_0=A_805 | ~m1_subset_1(E_808, k4_zfmisc_1(A_804, B_802, C_807, D_806)) | k1_xboole_0=D_806 | k1_xboole_0=C_807 | k1_xboole_0=B_802 | k1_xboole_0=A_804 | ~m1_subset_1(E_808, k4_zfmisc_1(A_804, B_802, C_807, D_806)) | k1_xboole_0=D_806 | k1_xboole_0=C_807 | k1_xboole_0=B_802 | k1_xboole_0=A_804)), inference(superposition, [status(thm), theory('equality')], [c_8, c_2187])).
% 7.89/2.86  tff(c_3051, plain, (![B_802, A_804, D_806, C_807]: (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_4'(B_802, A_804, D_806, C_807, '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_804, B_802, C_807, D_806)) | k1_xboole_0=D_806 | k1_xboole_0=C_807 | k1_xboole_0=B_802 | k1_xboole_0=A_804)), inference(resolution, [status(thm)], [c_32, c_3037])).
% 7.89/2.86  tff(c_3059, plain, (![B_810, A_811, D_812, C_813]: (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_4'(B_810, A_811, D_812, C_813, '#skF_9') | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_811, B_810, C_813, D_812)) | k1_xboole_0=D_812 | k1_xboole_0=C_813 | k1_xboole_0=B_810 | k1_xboole_0=A_811)), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_3051])).
% 7.89/2.86  tff(c_3062, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_4'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_32, c_3059])).
% 7.89/2.86  tff(c_3066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_1918, c_3062])).
% 7.89/2.86  tff(c_3067, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))!=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9') | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))!=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_1639])).
% 7.89/2.86  tff(c_3091, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))!=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_3067])).
% 7.89/2.86  tff(c_3468, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!='#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3467, c_3091])).
% 7.89/2.86  tff(c_22, plain, (![A_74, G_93, D_77, B_75, F_92, C_76, H_94, I_95]: (k9_mcart_1(A_74, B_75, C_76, D_77, k4_mcart_1(F_92, G_93, H_94, I_95))=G_93 | ~m1_subset_1(k4_mcart_1(F_92, G_93, H_94, I_95), k4_zfmisc_1(A_74, B_75, C_76, D_77)) | k1_xboole_0=D_77 | k1_xboole_0=C_76 | k1_xboole_0=B_75 | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.89/2.86  tff(c_3612, plain, (![D_1003, D_999, B_1000, E_1001, C_1005, A_1002, B_1007, C_1004, A_1006]: (k9_mcart_1(A_1006, B_1007, C_1004, D_1003, k4_mcart_1('#skF_1'(B_1000, A_1002, D_999, C_1005, E_1001), '#skF_2'(B_1000, A_1002, D_999, C_1005, E_1001), '#skF_3'(B_1000, A_1002, D_999, C_1005, E_1001), '#skF_4'(B_1000, A_1002, D_999, C_1005, E_1001)))='#skF_2'(B_1000, A_1002, D_999, C_1005, E_1001) | ~m1_subset_1(E_1001, k4_zfmisc_1(A_1006, B_1007, C_1004, D_1003)) | k1_xboole_0=D_1003 | k1_xboole_0=C_1004 | k1_xboole_0=B_1007 | k1_xboole_0=A_1006 | ~m1_subset_1(E_1001, k4_zfmisc_1(A_1002, B_1000, C_1005, D_999)) | k1_xboole_0=D_999 | k1_xboole_0=C_1005 | k1_xboole_0=B_1000 | k1_xboole_0=A_1002)), inference(superposition, [status(thm), theory('equality')], [c_3293, c_22])).
% 7.89/2.86  tff(c_4462, plain, (![B_1137, A_1138, D_1139, C_1142, D_1143, A_1141, E_1145, B_1140, C_1144]: (k9_mcart_1(A_1138, B_1140, C_1142, D_1139, E_1145)='#skF_2'(B_1137, A_1141, D_1143, C_1144, E_1145) | ~m1_subset_1(E_1145, k4_zfmisc_1(A_1138, B_1140, C_1142, D_1139)) | k1_xboole_0=D_1139 | k1_xboole_0=C_1142 | k1_xboole_0=B_1140 | k1_xboole_0=A_1138 | ~m1_subset_1(E_1145, k4_zfmisc_1(A_1141, B_1137, C_1144, D_1143)) | k1_xboole_0=D_1143 | k1_xboole_0=C_1144 | k1_xboole_0=B_1137 | k1_xboole_0=A_1141 | ~m1_subset_1(E_1145, k4_zfmisc_1(A_1141, B_1137, C_1144, D_1143)) | k1_xboole_0=D_1143 | k1_xboole_0=C_1144 | k1_xboole_0=B_1137 | k1_xboole_0=A_1141)), inference(superposition, [status(thm), theory('equality')], [c_8, c_3612])).
% 7.89/2.86  tff(c_4476, plain, (![B_1137, A_1141, D_1143, C_1144]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_2'(B_1137, A_1141, D_1143, C_1144, '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_1141, B_1137, C_1144, D_1143)) | k1_xboole_0=D_1143 | k1_xboole_0=C_1144 | k1_xboole_0=B_1137 | k1_xboole_0=A_1141)), inference(resolution, [status(thm)], [c_32, c_4462])).
% 7.89/2.86  tff(c_4484, plain, (![B_1146, A_1147, D_1148, C_1149]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_2'(B_1146, A_1147, D_1148, C_1149, '#skF_9') | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_1147, B_1146, C_1149, D_1148)) | k1_xboole_0=D_1148 | k1_xboole_0=C_1149 | k1_xboole_0=B_1146 | k1_xboole_0=A_1147)), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_4476])).
% 7.89/2.86  tff(c_4487, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_2'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_32, c_4484])).
% 7.89/2.86  tff(c_4491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_3468, c_4487])).
% 7.89/2.86  tff(c_4492, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))!=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_3067])).
% 7.89/2.86  tff(c_4843, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!='#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4842, c_4492])).
% 7.89/2.86  tff(c_20, plain, (![A_74, G_93, D_77, B_75, F_92, C_76, H_94, I_95]: (k10_mcart_1(A_74, B_75, C_76, D_77, k4_mcart_1(F_92, G_93, H_94, I_95))=H_94 | ~m1_subset_1(k4_mcart_1(F_92, G_93, H_94, I_95), k4_zfmisc_1(A_74, B_75, C_76, D_77)) | k1_xboole_0=D_77 | k1_xboole_0=C_76 | k1_xboole_0=B_75 | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.89/2.86  tff(c_5294, plain, (![C_1396, B_1398, A_1397, D_1393, D_1394, E_1390, A_1391, C_1395, B_1392]: (k10_mcart_1(A_1397, B_1398, C_1395, D_1394, k4_mcart_1('#skF_1'(B_1392, A_1391, D_1393, C_1396, E_1390), '#skF_2'(B_1392, A_1391, D_1393, C_1396, E_1390), '#skF_3'(B_1392, A_1391, D_1393, C_1396, E_1390), '#skF_4'(B_1392, A_1391, D_1393, C_1396, E_1390)))='#skF_3'(B_1392, A_1391, D_1393, C_1396, E_1390) | ~m1_subset_1(E_1390, k4_zfmisc_1(A_1397, B_1398, C_1395, D_1394)) | k1_xboole_0=D_1394 | k1_xboole_0=C_1395 | k1_xboole_0=B_1398 | k1_xboole_0=A_1397 | ~m1_subset_1(E_1390, k4_zfmisc_1(A_1391, B_1392, C_1396, D_1393)) | k1_xboole_0=D_1393 | k1_xboole_0=C_1396 | k1_xboole_0=B_1392 | k1_xboole_0=A_1391)), inference(superposition, [status(thm), theory('equality')], [c_4716, c_20])).
% 7.89/2.86  tff(c_6503, plain, (![B_1571, A_1574, C_1572, A_1573, E_1579, D_1576, B_1575, D_1577, C_1578]: (k10_mcart_1(A_1573, B_1575, C_1572, D_1576, E_1579)='#skF_3'(B_1571, A_1574, D_1577, C_1578, E_1579) | ~m1_subset_1(E_1579, k4_zfmisc_1(A_1573, B_1575, C_1572, D_1576)) | k1_xboole_0=D_1576 | k1_xboole_0=C_1572 | k1_xboole_0=B_1575 | k1_xboole_0=A_1573 | ~m1_subset_1(E_1579, k4_zfmisc_1(A_1574, B_1571, C_1578, D_1577)) | k1_xboole_0=D_1577 | k1_xboole_0=C_1578 | k1_xboole_0=B_1571 | k1_xboole_0=A_1574 | ~m1_subset_1(E_1579, k4_zfmisc_1(A_1574, B_1571, C_1578, D_1577)) | k1_xboole_0=D_1577 | k1_xboole_0=C_1578 | k1_xboole_0=B_1571 | k1_xboole_0=A_1574)), inference(superposition, [status(thm), theory('equality')], [c_8, c_5294])).
% 7.89/2.86  tff(c_6517, plain, (![B_1571, A_1574, D_1577, C_1578]: (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_3'(B_1571, A_1574, D_1577, C_1578, '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_1574, B_1571, C_1578, D_1577)) | k1_xboole_0=D_1577 | k1_xboole_0=C_1578 | k1_xboole_0=B_1571 | k1_xboole_0=A_1574)), inference(resolution, [status(thm)], [c_32, c_6503])).
% 7.89/2.86  tff(c_6525, plain, (![B_1580, A_1581, D_1582, C_1583]: (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_3'(B_1580, A_1581, D_1582, C_1583, '#skF_9') | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_1581, B_1580, C_1583, D_1582)) | k1_xboole_0=D_1582 | k1_xboole_0=C_1583 | k1_xboole_0=B_1580 | k1_xboole_0=A_1581)), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_6517])).
% 7.89/2.86  tff(c_6528, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_3'('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_32, c_6525])).
% 7.89/2.86  tff(c_6532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_34, c_4843, c_6528])).
% 7.89/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.89/2.86  
% 7.89/2.86  Inference rules
% 7.89/2.86  ----------------------
% 7.89/2.86  #Ref     : 0
% 7.89/2.86  #Sup     : 1547
% 7.89/2.86  #Fact    : 0
% 7.89/2.86  #Define  : 0
% 7.89/2.86  #Split   : 3
% 7.89/2.86  #Chain   : 0
% 7.89/2.86  #Close   : 0
% 7.89/2.86  
% 7.89/2.86  Ordering : KBO
% 7.89/2.86  
% 7.89/2.86  Simplification rules
% 7.89/2.86  ----------------------
% 7.89/2.86  #Subsume      : 160
% 7.89/2.86  #Demod        : 900
% 7.89/2.86  #Tautology    : 466
% 7.89/2.86  #SimpNegUnit  : 31
% 7.89/2.86  #BackRed      : 11
% 7.89/2.86  
% 7.89/2.86  #Partial instantiations: 0
% 7.89/2.86  #Strategies tried      : 1
% 7.89/2.86  
% 7.89/2.86  Timing (in seconds)
% 7.89/2.86  ----------------------
% 7.89/2.86  Preprocessing        : 0.33
% 7.89/2.86  Parsing              : 0.17
% 7.89/2.86  CNF conversion       : 0.03
% 7.89/2.86  Main loop            : 1.71
% 7.89/2.86  Inferencing          : 0.70
% 7.89/2.86  Reduction            : 0.50
% 7.89/2.86  Demodulation         : 0.37
% 7.89/2.86  BG Simplification    : 0.10
% 7.89/2.86  Subsumption          : 0.31
% 7.89/2.86  Abstraction          : 0.16
% 7.89/2.86  MUC search           : 0.00
% 7.89/2.86  Cooper               : 0.00
% 7.89/2.86  Total                : 2.08
% 7.89/2.86  Index Insertion      : 0.00
% 7.89/2.86  Index Deletion       : 0.00
% 7.89/2.86  Index Matching       : 0.00
% 7.89/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
