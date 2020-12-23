%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:05 EST 2020

% Result     : Theorem 13.06s
% Output     : CNFRefutation 13.16s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 374 expanded)
%              Number of leaves         :   38 ( 147 expanded)
%              Depth                    :   15
%              Number of atoms          :  184 (1214 expanded)
%              Number of equality atoms :   92 ( 665 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_10746,plain,(
    ! [A_1305,B_1306,C_1307,D_1308] :
      ( k7_mcart_1(A_1305,B_1306,C_1307,D_1308) = k2_mcart_1(D_1308)
      | ~ m1_subset_1(D_1308,k3_zfmisc_1(A_1305,B_1306,C_1307))
      | k1_xboole_0 = C_1307
      | k1_xboole_0 = B_1306
      | k1_xboole_0 = A_1305 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10767,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_62,c_10746])).

tff(c_10774,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_54,c_10767])).

tff(c_52,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_10775,plain,(
    k2_mcart_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10774,c_52])).

tff(c_20,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( m1_subset_1(k7_mcart_1(A_26,B_27,C_28,D_29),C_28)
      | ~ m1_subset_1(D_29,k3_zfmisc_1(A_26,B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10779,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10774,c_20])).

tff(c_10783,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10779])).

tff(c_10296,plain,(
    ! [A_1211,B_1212,C_1213] : k2_zfmisc_1(k2_zfmisc_1(A_1211,B_1212),C_1213) = k3_zfmisc_1(A_1211,B_1212,C_1213) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10311,plain,(
    ! [A_1211,B_1212,C_1213] : v1_relat_1(k3_zfmisc_1(A_1211,B_1212,C_1213)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10296,c_8])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10441,plain,(
    ! [A_1240,B_1241] :
      ( k4_tarski(k1_mcart_1(A_1240),k2_mcart_1(A_1240)) = A_1240
      | ~ r2_hidden(A_1240,B_1241)
      | ~ v1_relat_1(B_1241) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12183,plain,(
    ! [A_1480,B_1481] :
      ( k4_tarski(k1_mcart_1(A_1480),k2_mcart_1(A_1480)) = A_1480
      | ~ v1_relat_1(B_1481)
      | v1_xboole_0(B_1481)
      | ~ m1_subset_1(A_1480,B_1481) ) ),
    inference(resolution,[status(thm)],[c_6,c_10441])).

tff(c_12193,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_12183])).

tff(c_12200,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10311,c_12193])).

tff(c_12201,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_12200])).

tff(c_10343,plain,(
    ! [A_1222,B_1223,C_1224,D_1225] : k2_zfmisc_1(k3_zfmisc_1(A_1222,B_1223,C_1224),D_1225) = k4_zfmisc_1(A_1222,B_1223,C_1224,D_1225) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( v1_xboole_0(k2_zfmisc_1(A_2,B_3))
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_11078,plain,(
    ! [A_1341,B_1342,C_1343,D_1344] :
      ( v1_xboole_0(k4_zfmisc_1(A_1341,B_1342,C_1343,D_1344))
      | ~ v1_xboole_0(k3_zfmisc_1(A_1341,B_1342,C_1343)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10343,c_4])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_11106,plain,(
    ! [A_1341,B_1342,C_1343,D_1344] :
      ( k4_zfmisc_1(A_1341,B_1342,C_1343,D_1344) = k1_xboole_0
      | ~ v1_xboole_0(k3_zfmisc_1(A_1341,B_1342,C_1343)) ) ),
    inference(resolution,[status(thm)],[c_11078,c_2])).

tff(c_12261,plain,(
    ! [D_1482] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_1482) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12201,c_11106])).

tff(c_38,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k4_zfmisc_1(A_45,B_46,C_47,D_48) != k1_xboole_0
      | k1_xboole_0 = D_48
      | k1_xboole_0 = C_47
      | k1_xboole_0 = B_46
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12271,plain,(
    ! [D_1482] :
      ( k1_xboole_0 = D_1482
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12261,c_38])).

tff(c_12293,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_54,c_12271])).

tff(c_12287,plain,(
    ! [D_1482] : k1_xboole_0 = D_1482 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_54,c_12271])).

tff(c_12831,plain,(
    ! [D_4663] : D_4663 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_12293,c_12287])).

tff(c_13329,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_12831,c_10775])).

tff(c_13330,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12200])).

tff(c_18,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( m1_subset_1(k6_mcart_1(A_22,B_23,C_24,D_25),B_23)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( m1_subset_1(k5_mcart_1(A_18,B_19,C_20,D_21),A_18)
      | ~ m1_subset_1(D_21,k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10815,plain,(
    ! [A_1314,B_1315,C_1316,D_1317] :
      ( k5_mcart_1(A_1314,B_1315,C_1316,D_1317) = k1_mcart_1(k1_mcart_1(D_1317))
      | ~ m1_subset_1(D_1317,k3_zfmisc_1(A_1314,B_1315,C_1316))
      | k1_xboole_0 = C_1316
      | k1_xboole_0 = B_1315
      | k1_xboole_0 = A_1314 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10836,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_62,c_10815])).

tff(c_10843,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_54,c_10836])).

tff(c_10926,plain,(
    ! [A_1328,B_1329,C_1330,D_1331] :
      ( k6_mcart_1(A_1328,B_1329,C_1330,D_1331) = k2_mcart_1(k1_mcart_1(D_1331))
      | ~ m1_subset_1(D_1331,k3_zfmisc_1(A_1328,B_1329,C_1330))
      | k1_xboole_0 = C_1330
      | k1_xboole_0 = B_1329
      | k1_xboole_0 = A_1328 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10947,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_62,c_10926])).

tff(c_10954,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_54,c_10947])).

tff(c_13331,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_12200])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13) = k3_zfmisc_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10230,plain,(
    ! [A_1197,B_1198,C_1199] :
      ( r2_hidden(k1_mcart_1(A_1197),B_1198)
      | ~ r2_hidden(A_1197,k2_zfmisc_1(B_1198,C_1199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13340,plain,(
    ! [A_7800,B_7801,C_7802] :
      ( r2_hidden(k1_mcart_1(A_7800),B_7801)
      | v1_xboole_0(k2_zfmisc_1(B_7801,C_7802))
      | ~ m1_subset_1(A_7800,k2_zfmisc_1(B_7801,C_7802)) ) ),
    inference(resolution,[status(thm)],[c_6,c_10230])).

tff(c_13353,plain,(
    ! [A_7800,A_11,B_12,C_13] :
      ( r2_hidden(k1_mcart_1(A_7800),k2_zfmisc_1(A_11,B_12))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13))
      | ~ m1_subset_1(A_7800,k3_zfmisc_1(A_11,B_12,C_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_13340])).

tff(c_19408,plain,(
    ! [A_8237,A_8238,B_8239,C_8240] :
      ( r2_hidden(k1_mcart_1(A_8237),k2_zfmisc_1(A_8238,B_8239))
      | v1_xboole_0(k3_zfmisc_1(A_8238,B_8239,C_8240))
      | ~ m1_subset_1(A_8237,k3_zfmisc_1(A_8238,B_8239,C_8240)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_13353])).

tff(c_19439,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_19408])).

tff(c_19455,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_13331,c_19439])).

tff(c_30,plain,(
    ! [A_38,B_39] :
      ( k4_tarski(k1_mcart_1(A_38),k2_mcart_1(A_38)) = A_38
      | ~ r2_hidden(A_38,B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_19457,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_19455,c_30])).

tff(c_19464,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10843,c_10954,c_19457])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k4_tarski(k4_tarski(A_8,B_9),C_10) = k3_mcart_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_19786,plain,(
    ! [C_8261] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_8261) = k4_tarski(k1_mcart_1('#skF_5'),C_8261) ),
    inference(superposition,[status(thm),theory(equality)],[c_19464,c_10])).

tff(c_60,plain,(
    ! [H_64,F_58,G_62] :
      ( H_64 = '#skF_4'
      | k3_mcart_1(F_58,G_62,H_64) != '#skF_5'
      | ~ m1_subset_1(H_64,'#skF_3')
      | ~ m1_subset_1(G_62,'#skF_2')
      | ~ m1_subset_1(F_58,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_19875,plain,(
    ! [C_8261] :
      ( C_8261 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_8261) != '#skF_5'
      | ~ m1_subset_1(C_8261,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19786,c_60])).

tff(c_19931,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_19875])).

tff(c_19934,plain,(
    ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_19931])).

tff(c_19938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_19934])).

tff(c_19939,plain,(
    ! [C_8261] :
      ( ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | C_8261 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_8261) != '#skF_5'
      | ~ m1_subset_1(C_8261,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_19875])).

tff(c_20034,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_19939])).

tff(c_20037,plain,(
    ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_20034])).

tff(c_20041,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_20037])).

tff(c_20047,plain,(
    ! [C_8281] :
      ( C_8281 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_8281) != '#skF_5'
      | ~ m1_subset_1(C_8281,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_19939])).

tff(c_20050,plain,
    ( k2_mcart_1('#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13330,c_20047])).

tff(c_20053,plain,(
    k2_mcart_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10783,c_20050])).

tff(c_20055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10775,c_20053])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:19:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.06/4.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.06/4.90  
% 13.06/4.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.16/4.90  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.16/4.90  
% 13.16/4.90  %Foreground sorts:
% 13.16/4.90  
% 13.16/4.90  
% 13.16/4.90  %Background operators:
% 13.16/4.90  
% 13.16/4.90  
% 13.16/4.90  %Foreground operators:
% 13.16/4.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.16/4.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.16/4.90  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.16/4.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.16/4.90  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 13.16/4.90  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 13.16/4.90  tff('#skF_5', type, '#skF_5': $i).
% 13.16/4.90  tff('#skF_2', type, '#skF_2': $i).
% 13.16/4.90  tff('#skF_3', type, '#skF_3': $i).
% 13.16/4.90  tff('#skF_1', type, '#skF_1': $i).
% 13.16/4.90  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 13.16/4.90  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 13.16/4.90  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 13.16/4.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.16/4.90  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 13.16/4.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.16/4.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.16/4.90  tff('#skF_4', type, '#skF_4': $i).
% 13.16/4.90  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 13.16/4.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.16/4.90  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 13.16/4.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.16/4.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.16/4.90  
% 13.16/4.92  tff(f_143, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 13.16/4.92  tff(f_100, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 13.16/4.92  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 13.16/4.92  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 13.16/4.92  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.16/4.92  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 13.16/4.92  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 13.16/4.92  tff(f_47, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 13.16/4.92  tff(f_33, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 13.16/4.92  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 13.16/4.92  tff(f_115, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 13.16/4.92  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k6_mcart_1(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 13.16/4.92  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k5_mcart_1(A, B, C, D), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 13.16/4.92  tff(f_65, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 13.16/4.92  tff(f_43, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 13.16/4.92  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.16/4.92  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.16/4.92  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.16/4.92  tff(c_62, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.16/4.92  tff(c_10746, plain, (![A_1305, B_1306, C_1307, D_1308]: (k7_mcart_1(A_1305, B_1306, C_1307, D_1308)=k2_mcart_1(D_1308) | ~m1_subset_1(D_1308, k3_zfmisc_1(A_1305, B_1306, C_1307)) | k1_xboole_0=C_1307 | k1_xboole_0=B_1306 | k1_xboole_0=A_1305)), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.16/4.92  tff(c_10767, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_62, c_10746])).
% 13.16/4.92  tff(c_10774, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_54, c_10767])).
% 13.16/4.92  tff(c_52, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.16/4.92  tff(c_10775, plain, (k2_mcart_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10774, c_52])).
% 13.16/4.92  tff(c_20, plain, (![A_26, B_27, C_28, D_29]: (m1_subset_1(k7_mcart_1(A_26, B_27, C_28, D_29), C_28) | ~m1_subset_1(D_29, k3_zfmisc_1(A_26, B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.16/4.92  tff(c_10779, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10774, c_20])).
% 13.16/4.92  tff(c_10783, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10779])).
% 13.16/4.92  tff(c_10296, plain, (![A_1211, B_1212, C_1213]: (k2_zfmisc_1(k2_zfmisc_1(A_1211, B_1212), C_1213)=k3_zfmisc_1(A_1211, B_1212, C_1213))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.16/4.92  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.16/4.92  tff(c_10311, plain, (![A_1211, B_1212, C_1213]: (v1_relat_1(k3_zfmisc_1(A_1211, B_1212, C_1213)))), inference(superposition, [status(thm), theory('equality')], [c_10296, c_8])).
% 13.16/4.92  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.16/4.92  tff(c_10441, plain, (![A_1240, B_1241]: (k4_tarski(k1_mcart_1(A_1240), k2_mcart_1(A_1240))=A_1240 | ~r2_hidden(A_1240, B_1241) | ~v1_relat_1(B_1241))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.16/4.92  tff(c_12183, plain, (![A_1480, B_1481]: (k4_tarski(k1_mcart_1(A_1480), k2_mcart_1(A_1480))=A_1480 | ~v1_relat_1(B_1481) | v1_xboole_0(B_1481) | ~m1_subset_1(A_1480, B_1481))), inference(resolution, [status(thm)], [c_6, c_10441])).
% 13.16/4.92  tff(c_12193, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_12183])).
% 13.16/4.92  tff(c_12200, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10311, c_12193])).
% 13.16/4.92  tff(c_12201, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_12200])).
% 13.16/4.92  tff(c_10343, plain, (![A_1222, B_1223, C_1224, D_1225]: (k2_zfmisc_1(k3_zfmisc_1(A_1222, B_1223, C_1224), D_1225)=k4_zfmisc_1(A_1222, B_1223, C_1224, D_1225))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.16/4.92  tff(c_4, plain, (![A_2, B_3]: (v1_xboole_0(k2_zfmisc_1(A_2, B_3)) | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.16/4.92  tff(c_11078, plain, (![A_1341, B_1342, C_1343, D_1344]: (v1_xboole_0(k4_zfmisc_1(A_1341, B_1342, C_1343, D_1344)) | ~v1_xboole_0(k3_zfmisc_1(A_1341, B_1342, C_1343)))), inference(superposition, [status(thm), theory('equality')], [c_10343, c_4])).
% 13.16/4.92  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.16/4.92  tff(c_11106, plain, (![A_1341, B_1342, C_1343, D_1344]: (k4_zfmisc_1(A_1341, B_1342, C_1343, D_1344)=k1_xboole_0 | ~v1_xboole_0(k3_zfmisc_1(A_1341, B_1342, C_1343)))), inference(resolution, [status(thm)], [c_11078, c_2])).
% 13.16/4.92  tff(c_12261, plain, (![D_1482]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_1482)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12201, c_11106])).
% 13.16/4.92  tff(c_38, plain, (![A_45, B_46, C_47, D_48]: (k4_zfmisc_1(A_45, B_46, C_47, D_48)!=k1_xboole_0 | k1_xboole_0=D_48 | k1_xboole_0=C_47 | k1_xboole_0=B_46 | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_115])).
% 13.16/4.92  tff(c_12271, plain, (![D_1482]: (k1_xboole_0=D_1482 | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12261, c_38])).
% 13.16/4.92  tff(c_12293, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_54, c_12271])).
% 13.16/4.92  tff(c_12287, plain, (![D_1482]: (k1_xboole_0=D_1482)), inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_54, c_12271])).
% 13.16/4.92  tff(c_12831, plain, (![D_4663]: (D_4663='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12293, c_12287])).
% 13.16/4.92  tff(c_13329, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_12831, c_10775])).
% 13.16/4.92  tff(c_13330, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_12200])).
% 13.16/4.92  tff(c_18, plain, (![A_22, B_23, C_24, D_25]: (m1_subset_1(k6_mcart_1(A_22, B_23, C_24, D_25), B_23) | ~m1_subset_1(D_25, k3_zfmisc_1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.16/4.92  tff(c_16, plain, (![A_18, B_19, C_20, D_21]: (m1_subset_1(k5_mcart_1(A_18, B_19, C_20, D_21), A_18) | ~m1_subset_1(D_21, k3_zfmisc_1(A_18, B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.16/4.92  tff(c_10815, plain, (![A_1314, B_1315, C_1316, D_1317]: (k5_mcart_1(A_1314, B_1315, C_1316, D_1317)=k1_mcart_1(k1_mcart_1(D_1317)) | ~m1_subset_1(D_1317, k3_zfmisc_1(A_1314, B_1315, C_1316)) | k1_xboole_0=C_1316 | k1_xboole_0=B_1315 | k1_xboole_0=A_1314)), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.16/4.92  tff(c_10836, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_62, c_10815])).
% 13.16/4.92  tff(c_10843, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_54, c_10836])).
% 13.16/4.92  tff(c_10926, plain, (![A_1328, B_1329, C_1330, D_1331]: (k6_mcart_1(A_1328, B_1329, C_1330, D_1331)=k2_mcart_1(k1_mcart_1(D_1331)) | ~m1_subset_1(D_1331, k3_zfmisc_1(A_1328, B_1329, C_1330)) | k1_xboole_0=C_1330 | k1_xboole_0=B_1329 | k1_xboole_0=A_1328)), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.16/4.92  tff(c_10947, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_62, c_10926])).
% 13.16/4.92  tff(c_10954, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_54, c_10947])).
% 13.16/4.92  tff(c_13331, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_12200])).
% 13.16/4.92  tff(c_12, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)=k3_zfmisc_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.16/4.92  tff(c_10230, plain, (![A_1197, B_1198, C_1199]: (r2_hidden(k1_mcart_1(A_1197), B_1198) | ~r2_hidden(A_1197, k2_zfmisc_1(B_1198, C_1199)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.16/4.92  tff(c_13340, plain, (![A_7800, B_7801, C_7802]: (r2_hidden(k1_mcart_1(A_7800), B_7801) | v1_xboole_0(k2_zfmisc_1(B_7801, C_7802)) | ~m1_subset_1(A_7800, k2_zfmisc_1(B_7801, C_7802)))), inference(resolution, [status(thm)], [c_6, c_10230])).
% 13.16/4.92  tff(c_13353, plain, (![A_7800, A_11, B_12, C_13]: (r2_hidden(k1_mcart_1(A_7800), k2_zfmisc_1(A_11, B_12)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)) | ~m1_subset_1(A_7800, k3_zfmisc_1(A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_13340])).
% 13.16/4.92  tff(c_19408, plain, (![A_8237, A_8238, B_8239, C_8240]: (r2_hidden(k1_mcart_1(A_8237), k2_zfmisc_1(A_8238, B_8239)) | v1_xboole_0(k3_zfmisc_1(A_8238, B_8239, C_8240)) | ~m1_subset_1(A_8237, k3_zfmisc_1(A_8238, B_8239, C_8240)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_13353])).
% 13.16/4.92  tff(c_19439, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_19408])).
% 13.16/4.92  tff(c_19455, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_13331, c_19439])).
% 13.16/4.92  tff(c_30, plain, (![A_38, B_39]: (k4_tarski(k1_mcart_1(A_38), k2_mcart_1(A_38))=A_38 | ~r2_hidden(A_38, B_39) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.16/4.92  tff(c_19457, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_19455, c_30])).
% 13.16/4.92  tff(c_19464, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10843, c_10954, c_19457])).
% 13.16/4.92  tff(c_10, plain, (![A_8, B_9, C_10]: (k4_tarski(k4_tarski(A_8, B_9), C_10)=k3_mcart_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.16/4.92  tff(c_19786, plain, (![C_8261]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_8261)=k4_tarski(k1_mcart_1('#skF_5'), C_8261))), inference(superposition, [status(thm), theory('equality')], [c_19464, c_10])).
% 13.16/4.92  tff(c_60, plain, (![H_64, F_58, G_62]: (H_64='#skF_4' | k3_mcart_1(F_58, G_62, H_64)!='#skF_5' | ~m1_subset_1(H_64, '#skF_3') | ~m1_subset_1(G_62, '#skF_2') | ~m1_subset_1(F_58, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.16/4.92  tff(c_19875, plain, (![C_8261]: (C_8261='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_8261)!='#skF_5' | ~m1_subset_1(C_8261, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_19786, c_60])).
% 13.16/4.92  tff(c_19931, plain, (~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(splitLeft, [status(thm)], [c_19875])).
% 13.16/4.92  tff(c_19934, plain, (~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_19931])).
% 13.16/4.92  tff(c_19938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_19934])).
% 13.16/4.92  tff(c_19939, plain, (![C_8261]: (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | C_8261='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_8261)!='#skF_5' | ~m1_subset_1(C_8261, '#skF_3'))), inference(splitRight, [status(thm)], [c_19875])).
% 13.16/4.92  tff(c_20034, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_19939])).
% 13.16/4.92  tff(c_20037, plain, (~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_20034])).
% 13.16/4.92  tff(c_20041, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_20037])).
% 13.16/4.92  tff(c_20047, plain, (![C_8281]: (C_8281='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_8281)!='#skF_5' | ~m1_subset_1(C_8281, '#skF_3'))), inference(splitRight, [status(thm)], [c_19939])).
% 13.16/4.92  tff(c_20050, plain, (k2_mcart_1('#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13330, c_20047])).
% 13.16/4.92  tff(c_20053, plain, (k2_mcart_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10783, c_20050])).
% 13.16/4.92  tff(c_20055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10775, c_20053])).
% 13.16/4.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.16/4.92  
% 13.16/4.92  Inference rules
% 13.16/4.92  ----------------------
% 13.16/4.92  #Ref     : 0
% 13.16/4.92  #Sup     : 5921
% 13.16/4.92  #Fact    : 0
% 13.16/4.92  #Define  : 0
% 13.16/4.92  #Split   : 19
% 13.16/4.92  #Chain   : 0
% 13.16/4.92  #Close   : 0
% 13.16/4.92  
% 13.16/4.92  Ordering : KBO
% 13.16/4.92  
% 13.16/4.92  Simplification rules
% 13.16/4.92  ----------------------
% 13.16/4.92  #Subsume      : 1441
% 13.16/4.92  #Demod        : 2021
% 13.16/4.92  #Tautology    : 1013
% 13.16/4.92  #SimpNegUnit  : 45
% 13.16/4.92  #BackRed      : 19
% 13.16/4.92  
% 13.16/4.92  #Partial instantiations: 565
% 13.16/4.92  #Strategies tried      : 1
% 13.16/4.92  
% 13.16/4.92  Timing (in seconds)
% 13.16/4.92  ----------------------
% 13.16/4.92  Preprocessing        : 0.42
% 13.16/4.92  Parsing              : 0.21
% 13.16/4.92  CNF conversion       : 0.03
% 13.16/4.92  Main loop            : 3.66
% 13.16/4.92  Inferencing          : 1.08
% 13.16/4.92  Reduction            : 1.06
% 13.16/4.92  Demodulation         : 0.72
% 13.16/4.92  BG Simplification    : 0.13
% 13.16/4.92  Subsumption          : 1.15
% 13.16/4.92  Abstraction          : 0.17
% 13.16/4.92  MUC search           : 0.00
% 13.16/4.92  Cooper               : 0.00
% 13.16/4.92  Total                : 4.12
% 13.16/4.92  Index Insertion      : 0.00
% 13.16/4.92  Index Deletion       : 0.00
% 13.16/4.92  Index Matching       : 0.00
% 13.16/4.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
