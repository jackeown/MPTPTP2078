%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:28 EST 2020

% Result     : Theorem 10.14s
% Output     : CNFRefutation 10.47s
% Verified   : 
% Statistics : Number of formulae       :  295 (1673 expanded)
%              Number of leaves         :   37 ( 530 expanded)
%              Depth                    :   20
%              Number of atoms          :  456 (4063 expanded)
%              Number of equality atoms :  188 (2807 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_zfmisc_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_14 > #skF_13 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_12

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | ( A = D
            & B = E
            & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

tff(f_101,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_70,plain,(
    k3_zfmisc_1('#skF_9','#skF_10','#skF_11') = k3_zfmisc_1('#skF_12','#skF_13','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_60,plain,(
    ! [A_57,B_58,C_59] : k2_zfmisc_1(k2_zfmisc_1(A_57,B_58),C_59) = k3_zfmisc_1(A_57,B_58,C_59) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    ! [A_12,B_13,D_39] :
      ( r2_hidden('#skF_7'(A_12,B_13,k2_zfmisc_1(A_12,B_13),D_39),A_12)
      | ~ r2_hidden(D_39,k2_zfmisc_1(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1147,plain,(
    ! [A_1149,B_1150,D_1151] :
      ( r2_hidden('#skF_7'(A_1149,B_1150,k2_zfmisc_1(A_1149,B_1150),D_1151),A_1149)
      | ~ r2_hidden(D_1151,k2_zfmisc_1(A_1149,B_1150)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1606,plain,(
    ! [A_1166,D_1167,B_1168] :
      ( ~ v1_xboole_0(A_1166)
      | ~ r2_hidden(D_1167,k2_zfmisc_1(A_1166,B_1168)) ) ),
    inference(resolution,[status(thm)],[c_1147,c_2])).

tff(c_1629,plain,(
    ! [A_1166,D_39,B_1168,B_13] :
      ( ~ v1_xboole_0(A_1166)
      | ~ r2_hidden(D_39,k2_zfmisc_1(k2_zfmisc_1(A_1166,B_1168),B_13)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1606])).

tff(c_1920,plain,(
    ! [A_1188,D_1189,B_1190,B_1191] :
      ( ~ v1_xboole_0(A_1188)
      | ~ r2_hidden(D_1189,k3_zfmisc_1(A_1188,B_1190,B_1191)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1629])).

tff(c_1975,plain,(
    ! [D_1189] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ r2_hidden(D_1189,k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1920])).

tff(c_1988,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1975])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_950,plain,(
    ! [A_1133,B_1134,D_1135] :
      ( r2_hidden('#skF_8'(A_1133,B_1134,k2_zfmisc_1(A_1133,B_1134),D_1135),B_1134)
      | ~ r2_hidden(D_1135,k2_zfmisc_1(A_1133,B_1134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_969,plain,(
    ! [B_1134,D_1135,A_1133] :
      ( ~ v1_xboole_0(B_1134)
      | ~ r2_hidden(D_1135,k2_zfmisc_1(A_1133,B_1134)) ) ),
    inference(resolution,[status(thm)],[c_950,c_2])).

tff(c_1163,plain,(
    ! [B_1134,D_1151,A_1133,B_1150] :
      ( ~ v1_xboole_0(B_1134)
      | ~ r2_hidden(D_1151,k2_zfmisc_1(k2_zfmisc_1(A_1133,B_1134),B_1150)) ) ),
    inference(resolution,[status(thm)],[c_1147,c_969])).

tff(c_2038,plain,(
    ! [B_1195,D_1196,A_1197,B_1198] :
      ( ~ v1_xboole_0(B_1195)
      | ~ r2_hidden(D_1196,k3_zfmisc_1(A_1197,B_1195,B_1198)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1163])).

tff(c_2106,plain,(
    ! [B_1199,A_1200,B_1201] :
      ( ~ v1_xboole_0(B_1199)
      | v1_xboole_0(k3_zfmisc_1(A_1200,B_1199,B_1201)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2038])).

tff(c_2140,plain,
    ( ~ v1_xboole_0('#skF_10')
    | v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2106])).

tff(c_2155,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2140])).

tff(c_197,plain,(
    ! [A_89,B_90,C_91] : k2_zfmisc_1(k2_zfmisc_1(A_89,B_90),C_91) = k3_zfmisc_1(A_89,B_90,C_91) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    ! [A_46,B_47] :
      ( v1_xboole_0(k2_zfmisc_1(A_46,B_47))
      | ~ v1_xboole_0(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_219,plain,(
    ! [A_89,B_90,C_91] :
      ( v1_xboole_0(k3_zfmisc_1(A_89,B_90,C_91))
      | ~ v1_xboole_0(C_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_44])).

tff(c_1675,plain,(
    ! [A_1169,B_1170] :
      ( ~ v1_xboole_0(A_1169)
      | v1_xboole_0(k2_zfmisc_1(A_1169,B_1170)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1606])).

tff(c_2949,plain,(
    ! [A_1249,B_1250,C_1251] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_1249,B_1250))
      | v1_xboole_0(k3_zfmisc_1(A_1249,B_1250,C_1251)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1675])).

tff(c_2985,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'))
    | v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2949])).

tff(c_3498,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_2985])).

tff(c_243,plain,(
    ! [A_94,B_95,C_96] :
      ( v1_xboole_0(k3_zfmisc_1(A_94,B_95,C_96))
      | ~ v1_xboole_0(C_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_44])).

tff(c_256,plain,
    ( v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14'))
    | ~ v1_xboole_0('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_243])).

tff(c_262,plain,(
    ~ v1_xboole_0('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_54,plain,(
    ! [A_53,B_54] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_53,B_54))
      | v1_xboole_0(B_54)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5612,plain,(
    ! [A_1341,B_1342,C_1343] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_1341,B_1342,C_1343))
      | v1_xboole_0(C_1343)
      | v1_xboole_0(k2_zfmisc_1(A_1341,B_1342)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_54])).

tff(c_5660,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14'))
    | v1_xboole_0('#skF_11')
    | v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_5612])).

tff(c_5685,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(negUnitSimplification,[status(thm)],[c_3498,c_262,c_5660])).

tff(c_5701,plain,(
    ~ v1_xboole_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_219,c_5685])).

tff(c_2105,plain,(
    ! [B_1195,A_1197,B_1198] :
      ( ~ v1_xboole_0(B_1195)
      | v1_xboole_0(k3_zfmisc_1(A_1197,B_1195,B_1198)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2038])).

tff(c_5699,plain,(
    ~ v1_xboole_0('#skF_13') ),
    inference(resolution,[status(thm)],[c_2105,c_5685])).

tff(c_1987,plain,(
    ! [A_1188,B_1190,B_1191] :
      ( ~ v1_xboole_0(A_1188)
      | v1_xboole_0(k3_zfmisc_1(A_1188,B_1190,B_1191)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1920])).

tff(c_5700,plain,(
    ~ v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_1987,c_5685])).

tff(c_62,plain,
    ( '#skF_11' != '#skF_14'
    | '#skF_10' != '#skF_13'
    | '#skF_9' != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_75,plain,(
    '#skF_9' != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_412,plain,(
    ! [A_116,B_117] :
      ( k2_relat_1(k2_zfmisc_1(A_116,B_117)) = B_117
      | k1_xboole_0 = B_117
      | k1_xboole_0 = A_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_7219,plain,(
    ! [A_1407,B_1408,C_1409] :
      ( k2_relat_1(k3_zfmisc_1(A_1407,B_1408,C_1409)) = C_1409
      | k1_xboole_0 = C_1409
      | k2_zfmisc_1(A_1407,B_1408) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_412])).

tff(c_7252,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) = '#skF_11'
    | k1_xboole_0 = '#skF_11'
    | k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_7219])).

tff(c_7259,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) = '#skF_11'
    | k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7252])).

tff(c_7394,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7259])).

tff(c_7395,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7394,c_3498])).

tff(c_7398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_7395])).

tff(c_7399,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_7259])).

tff(c_424,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_relat_1(k3_zfmisc_1(A_57,B_58,C_59)) = C_59
      | k1_xboole_0 = C_59
      | k2_zfmisc_1(A_57,B_58) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_412])).

tff(c_7404,plain,
    ( '#skF_11' = '#skF_14'
    | k1_xboole_0 = '#skF_14'
    | k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7399,c_424])).

tff(c_7411,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7404])).

tff(c_1707,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_57,B_58))
      | v1_xboole_0(k3_zfmisc_1(A_57,B_58,C_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1675])).

tff(c_5698,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_1707,c_5685])).

tff(c_7412,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7411,c_5698])).

tff(c_7415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_7412])).

tff(c_7417,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7404])).

tff(c_7416,plain,
    ( k1_xboole_0 = '#skF_14'
    | '#skF_11' = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_7404])).

tff(c_7418,plain,(
    '#skF_11' = '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_7416])).

tff(c_7423,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7418,c_64])).

tff(c_7400,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7259])).

tff(c_7422,plain,(
    k3_zfmisc_1('#skF_9','#skF_10','#skF_14') = k3_zfmisc_1('#skF_12','#skF_13','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7418,c_70])).

tff(c_322,plain,(
    ! [A_105,B_106] :
      ( k1_relat_1(k2_zfmisc_1(A_105,B_106)) = A_105
      | k1_xboole_0 = B_106
      | k1_xboole_0 = A_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12302,plain,(
    ! [A_1564,B_1565,C_1566] :
      ( k1_relat_1(k3_zfmisc_1(A_1564,B_1565,C_1566)) = k2_zfmisc_1(A_1564,B_1565)
      | k1_xboole_0 = C_1566
      | k2_zfmisc_1(A_1564,B_1565) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_322])).

tff(c_12317,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) = k2_zfmisc_1('#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_14'
    | k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7422,c_12302])).

tff(c_12344,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_7400,c_7423,c_12317])).

tff(c_331,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relat_1(k3_zfmisc_1(A_57,B_58,C_59)) = k2_zfmisc_1(A_57,B_58)
      | k1_xboole_0 = C_59
      | k2_zfmisc_1(A_57,B_58) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_322])).

tff(c_12352,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') = k2_zfmisc_1('#skF_12','#skF_13')
    | k1_xboole_0 = '#skF_14'
    | k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12344,c_331])).

tff(c_12358,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k2_zfmisc_1('#skF_12','#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_7417,c_7423,c_12352])).

tff(c_58,plain,(
    ! [A_55,B_56] :
      ( k1_relat_1(k2_zfmisc_1(A_55,B_56)) = A_55
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12512,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_12','#skF_13')) = '#skF_9'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_12358,c_58])).

tff(c_12545,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_12','#skF_13')) = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_66,c_12512])).

tff(c_12565,plain,
    ( '#skF_9' = '#skF_12'
    | k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_12545,c_58])).

tff(c_12571,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_12565])).

tff(c_12574,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_12571])).

tff(c_12621,plain,(
    v1_xboole_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12574,c_12])).

tff(c_12625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5700,c_12621])).

tff(c_12626,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_12571])).

tff(c_12675,plain,(
    v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12626,c_12])).

tff(c_12679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5699,c_12675])).

tff(c_12680,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_7416])).

tff(c_12722,plain,(
    v1_xboole_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12680,c_12])).

tff(c_12727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5701,c_12722])).

tff(c_12729,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_2985])).

tff(c_12762,plain,
    ( v1_xboole_0('#skF_10')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_12729,c_54])).

tff(c_12782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1988,c_2155,c_12762])).

tff(c_12784,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_2140])).

tff(c_94,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_2'(A_72,B_73),A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_104,plain,(
    ! [A_76,B_77] :
      ( ~ v1_xboole_0(A_76)
      | r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_50,plain,(
    ! [A_51,B_52] :
      ( ~ r1_tarski(A_51,k2_zfmisc_1(B_52,A_51))
      | k1_xboole_0 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_116,plain,(
    ! [A_76] :
      ( k1_xboole_0 = A_76
      | ~ v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_104,c_50])).

tff(c_12803,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_12784,c_116])).

tff(c_12815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_12803])).

tff(c_12817,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1975])).

tff(c_12836,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_12817,c_116])).

tff(c_12848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_12836])).

tff(c_12850,plain,(
    v1_xboole_0('#skF_11') ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_12857,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_12850,c_116])).

tff(c_12863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_12857])).

tff(c_12865,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_12866,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12865,c_68])).

tff(c_12879,plain,(
    k3_zfmisc_1('#skF_12','#skF_10','#skF_11') = k3_zfmisc_1('#skF_12','#skF_13','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12865,c_70])).

tff(c_13812,plain,(
    ! [A_2597,B_2598,D_2599] :
      ( r2_hidden('#skF_8'(A_2597,B_2598,k2_zfmisc_1(A_2597,B_2598),D_2599),B_2598)
      | ~ r2_hidden(D_2599,k2_zfmisc_1(A_2597,B_2598)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14200,plain,(
    ! [B_2616,D_2617,A_2618] :
      ( ~ v1_xboole_0(B_2616)
      | ~ r2_hidden(D_2617,k2_zfmisc_1(A_2618,B_2616)) ) ),
    inference(resolution,[status(thm)],[c_13812,c_2])).

tff(c_14227,plain,(
    ! [B_2616,D_39,A_2618,B_13] :
      ( ~ v1_xboole_0(B_2616)
      | ~ r2_hidden(D_39,k2_zfmisc_1(k2_zfmisc_1(A_2618,B_2616),B_13)) ) ),
    inference(resolution,[status(thm)],[c_26,c_14200])).

tff(c_14693,plain,(
    ! [B_2653,D_2654,A_2655,B_2656] :
      ( ~ v1_xboole_0(B_2653)
      | ~ r2_hidden(D_2654,k3_zfmisc_1(A_2655,B_2653,B_2656)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_14227])).

tff(c_14762,plain,(
    ! [B_2662,A_2663,B_2664] :
      ( ~ v1_xboole_0(B_2662)
      | v1_xboole_0(k3_zfmisc_1(A_2663,B_2662,B_2664)) ) ),
    inference(resolution,[status(thm)],[c_4,c_14693])).

tff(c_14796,plain,
    ( ~ v1_xboole_0('#skF_10')
    | v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12879,c_14762])).

tff(c_14811,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_14796])).

tff(c_13083,plain,(
    ! [A_1609,B_1610,C_1611] : k2_zfmisc_1(k2_zfmisc_1(A_1609,B_1610),C_1611) = k3_zfmisc_1(A_1609,B_1610,C_1611) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_13118,plain,(
    ! [A_1609,B_1610,C_1611] :
      ( v1_xboole_0(k3_zfmisc_1(A_1609,B_1610,C_1611))
      | ~ v1_xboole_0(C_1611) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13083,c_44])).

tff(c_13647,plain,(
    ! [A_2587,B_2588,D_2589] :
      ( r2_hidden('#skF_7'(A_2587,B_2588,k2_zfmisc_1(A_2587,B_2588),D_2589),A_2587)
      | ~ r2_hidden(D_2589,k2_zfmisc_1(A_2587,B_2588)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_13669,plain,(
    ! [A_2590,D_2591,B_2592] :
      ( ~ v1_xboole_0(A_2590)
      | ~ r2_hidden(D_2591,k2_zfmisc_1(A_2590,B_2592)) ) ),
    inference(resolution,[status(thm)],[c_13647,c_2])).

tff(c_14098,plain,(
    ! [A_2609,B_2610] :
      ( ~ v1_xboole_0(A_2609)
      | v1_xboole_0(k2_zfmisc_1(A_2609,B_2610)) ) ),
    inference(resolution,[status(thm)],[c_4,c_13669])).

tff(c_15853,plain,(
    ! [A_2724,B_2725,C_2726] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_2724,B_2725))
      | v1_xboole_0(k3_zfmisc_1(A_2724,B_2725,C_2726)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_14098])).

tff(c_15889,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10'))
    | v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12879,c_15853])).

tff(c_16597,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_15889])).

tff(c_13149,plain,(
    ! [A_1614,B_1615,C_1616] :
      ( v1_xboole_0(k3_zfmisc_1(A_1614,B_1615,C_1616))
      | ~ v1_xboole_0(C_1616) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13083,c_44])).

tff(c_13164,plain,
    ( v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14'))
    | ~ v1_xboole_0('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_12879,c_13149])).

tff(c_13171,plain,(
    ~ v1_xboole_0('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_13164])).

tff(c_18047,plain,(
    ! [A_2794,B_2795,C_2796] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_2794,B_2795,C_2796))
      | v1_xboole_0(C_2796)
      | v1_xboole_0(k2_zfmisc_1(A_2794,B_2795)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13083,c_54])).

tff(c_18089,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14'))
    | v1_xboole_0('#skF_11')
    | v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12879,c_18047])).

tff(c_18110,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(negUnitSimplification,[status(thm)],[c_16597,c_13171,c_18089])).

tff(c_18126,plain,(
    ~ v1_xboole_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_13118,c_18110])).

tff(c_12864,plain,
    ( '#skF_10' != '#skF_13'
    | '#skF_11' != '#skF_14' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_12871,plain,(
    '#skF_11' != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_12864])).

tff(c_12890,plain,(
    ! [A_1581,B_1582] :
      ( r2_hidden('#skF_2'(A_1581,B_1582),A_1581)
      | r1_tarski(A_1581,B_1582) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12901,plain,(
    ! [A_1583,B_1584] :
      ( ~ v1_xboole_0(A_1583)
      | r1_tarski(A_1583,B_1584) ) ),
    inference(resolution,[status(thm)],[c_12890,c_2])).

tff(c_52,plain,(
    ! [A_51,B_52] :
      ( ~ r1_tarski(A_51,k2_zfmisc_1(A_51,B_52))
      | k1_xboole_0 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12912,plain,(
    ! [A_1585] :
      ( k1_xboole_0 = A_1585
      | ~ v1_xboole_0(A_1585) ) ),
    inference(resolution,[status(thm)],[c_12901,c_52])).

tff(c_12922,plain,(
    ! [A_1586,B_1587] :
      ( k2_zfmisc_1(A_1586,B_1587) = k1_xboole_0
      | ~ v1_xboole_0(B_1587) ) ),
    inference(resolution,[status(thm)],[c_44,c_12912])).

tff(c_12928,plain,(
    ! [A_1586] : k2_zfmisc_1(A_1586,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_12922])).

tff(c_12900,plain,(
    ! [A_1581,B_1582] :
      ( ~ v1_xboole_0(A_1581)
      | r1_tarski(A_1581,B_1582) ) ),
    inference(resolution,[status(thm)],[c_12890,c_2])).

tff(c_13295,plain,(
    ! [A_1635,B_1636,C_1637] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1635,B_1636),k2_zfmisc_1(A_1635,C_1637))
      | r1_tarski(B_1636,C_1637)
      | k1_xboole_0 = A_1635 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_13326,plain,(
    ! [B_1638,C_1639,A_1640] :
      ( r1_tarski(B_1638,C_1639)
      | k1_xboole_0 = A_1640
      | ~ v1_xboole_0(k2_zfmisc_1(A_1640,B_1638)) ) ),
    inference(resolution,[status(thm)],[c_12900,c_13295])).

tff(c_13332,plain,(
    ! [C_1639,A_1586] :
      ( r1_tarski(k1_xboole_0,C_1639)
      | k1_xboole_0 = A_1586
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12928,c_13326])).

tff(c_13338,plain,(
    ! [C_1639,A_1586] :
      ( r1_tarski(k1_xboole_0,C_1639)
      | k1_xboole_0 = A_1586 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_13332])).

tff(c_13424,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_13338])).

tff(c_13425,plain,(
    v1_xboole_0('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_13424,c_12])).

tff(c_13454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13171,c_13425])).

tff(c_13455,plain,(
    ! [C_1639] : r1_tarski(k1_xboole_0,C_1639) ),
    inference(splitRight,[status(thm)],[c_13338])).

tff(c_56,plain,(
    ! [A_55,B_56] :
      ( k2_relat_1(k2_zfmisc_1(A_55,B_56)) = B_56
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_24015,plain,(
    ! [A_3008,B_3009,C_3010] :
      ( k2_relat_1(k3_zfmisc_1(A_3008,B_3009,C_3010)) = C_3010
      | k1_xboole_0 = C_3010
      | k2_zfmisc_1(A_3008,B_3009) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13083,c_56])).

tff(c_24051,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) = '#skF_11'
    | k1_xboole_0 = '#skF_11'
    | k2_zfmisc_1('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12879,c_24015])).

tff(c_24058,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) = '#skF_11'
    | k2_zfmisc_1('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_24051])).

tff(c_24059,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24058])).

tff(c_20000,plain,(
    ! [A_2868,B_2869,C_2870] :
      ( ~ r1_tarski(k2_zfmisc_1(A_2868,B_2869),k3_zfmisc_1(A_2868,B_2869,C_2870))
      | k2_zfmisc_1(A_2868,B_2869) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13083,c_52])).

tff(c_20079,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_12','#skF_10'),k3_zfmisc_1('#skF_12','#skF_13','#skF_14'))
    | k2_zfmisc_1('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12879,c_20000])).

tff(c_20455,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_12','#skF_10'),k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_20079])).

tff(c_24060,plain,(
    ~ r1_tarski(k1_xboole_0,k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24059,c_20455])).

tff(c_24064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13455,c_24060])).

tff(c_24065,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_24058])).

tff(c_13102,plain,(
    ! [A_1609,B_1610,C_1611] :
      ( k2_relat_1(k3_zfmisc_1(A_1609,B_1610,C_1611)) = C_1611
      | k1_xboole_0 = C_1611
      | k2_zfmisc_1(A_1609,B_1610) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13083,c_56])).

tff(c_24070,plain,
    ( '#skF_11' = '#skF_14'
    | k1_xboole_0 = '#skF_14'
    | k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24065,c_13102])).

tff(c_24076,plain,
    ( k1_xboole_0 = '#skF_14'
    | k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_12871,c_24070])).

tff(c_24079,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24076])).

tff(c_14127,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_57,B_58))
      | v1_xboole_0(k3_zfmisc_1(A_57,B_58,C_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_14098])).

tff(c_18123,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_14127,c_18110])).

tff(c_24080,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24079,c_18123])).

tff(c_24083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_24080])).

tff(c_24084,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_24076])).

tff(c_24129,plain,(
    v1_xboole_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24084,c_12])).

tff(c_24133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18126,c_24129])).

tff(c_24134,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20079])).

tff(c_24136,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24134,c_16597])).

tff(c_24139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_24136])).

tff(c_24141,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_15889])).

tff(c_24175,plain,
    ( v1_xboole_0('#skF_10')
    | v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_24141,c_54])).

tff(c_24197,plain,(
    v1_xboole_0('#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_14811,c_24175])).

tff(c_12910,plain,(
    ! [A_1583] :
      ( k1_xboole_0 = A_1583
      | ~ v1_xboole_0(A_1583) ) ),
    inference(resolution,[status(thm)],[c_12901,c_52])).

tff(c_24275,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_24197,c_12910])).

tff(c_24290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12866,c_24275])).

tff(c_24292,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_14796])).

tff(c_24311,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_24292,c_12910])).

tff(c_24323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_24311])).

tff(c_24325,plain,(
    v1_xboole_0('#skF_11') ),
    inference(splitRight,[status(thm)],[c_13164])).

tff(c_24334,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_24325,c_12910])).

tff(c_24341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_24334])).

tff(c_24343,plain,(
    '#skF_11' = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_12864])).

tff(c_24344,plain,(
    k3_zfmisc_1('#skF_12','#skF_10','#skF_11') = k3_zfmisc_1('#skF_12','#skF_13','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12865,c_70])).

tff(c_24349,plain,(
    k3_zfmisc_1('#skF_12','#skF_10','#skF_14') = k3_zfmisc_1('#skF_12','#skF_13','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24343,c_24344])).

tff(c_25016,plain,(
    ! [A_3096,B_3097,D_3098] :
      ( r2_hidden('#skF_7'(A_3096,B_3097,k2_zfmisc_1(A_3096,B_3097),D_3098),A_3096)
      | ~ r2_hidden(D_3098,k2_zfmisc_1(A_3096,B_3097)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24824,plain,(
    ! [A_3084,B_3085,D_3086] :
      ( r2_hidden('#skF_8'(A_3084,B_3085,k2_zfmisc_1(A_3084,B_3085),D_3086),B_3085)
      | ~ r2_hidden(D_3086,k2_zfmisc_1(A_3084,B_3085)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24840,plain,(
    ! [B_3085,D_3086,A_3084] :
      ( ~ v1_xboole_0(B_3085)
      | ~ r2_hidden(D_3086,k2_zfmisc_1(A_3084,B_3085)) ) ),
    inference(resolution,[status(thm)],[c_24824,c_2])).

tff(c_25024,plain,(
    ! [B_3085,D_3098,A_3084,B_3097] :
      ( ~ v1_xboole_0(B_3085)
      | ~ r2_hidden(D_3098,k2_zfmisc_1(k2_zfmisc_1(A_3084,B_3085),B_3097)) ) ),
    inference(resolution,[status(thm)],[c_25016,c_24840])).

tff(c_25625,plain,(
    ! [B_3135,D_3136,A_3137,B_3138] :
      ( ~ v1_xboole_0(B_3135)
      | ~ r2_hidden(D_3136,k3_zfmisc_1(A_3137,B_3135,B_3138)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_25024])).

tff(c_25673,plain,(
    ! [D_3136] :
      ( ~ v1_xboole_0('#skF_10')
      | ~ r2_hidden(D_3136,k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24349,c_25625])).

tff(c_25690,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_25673])).

tff(c_25689,plain,(
    ! [B_3135,A_3137,B_3138] :
      ( ~ v1_xboole_0(B_3135)
      | v1_xboole_0(k3_zfmisc_1(A_3137,B_3135,B_3138)) ) ),
    inference(resolution,[status(thm)],[c_4,c_25625])).

tff(c_25329,plain,(
    ! [A_3113,D_3114,B_3115] :
      ( ~ v1_xboole_0(A_3113)
      | ~ r2_hidden(D_3114,k2_zfmisc_1(A_3113,B_3115)) ) ),
    inference(resolution,[status(thm)],[c_25016,c_2])).

tff(c_25389,plain,(
    ! [A_3116,B_3117] :
      ( ~ v1_xboole_0(A_3116)
      | v1_xboole_0(k2_zfmisc_1(A_3116,B_3117)) ) ),
    inference(resolution,[status(thm)],[c_4,c_25329])).

tff(c_26823,plain,(
    ! [A_3221,B_3222,C_3223] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_3221,B_3222))
      | v1_xboole_0(k3_zfmisc_1(A_3221,B_3222,C_3223)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_25389])).

tff(c_26854,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10'))
    | v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24349,c_26823])).

tff(c_27019,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_26854])).

tff(c_24366,plain,(
    ! [A_3019,B_3020] :
      ( r2_hidden('#skF_2'(A_3019,B_3020),A_3019)
      | r1_tarski(A_3019,B_3020) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24370,plain,(
    ! [A_3019,B_3020] :
      ( ~ v1_xboole_0(A_3019)
      | r1_tarski(A_3019,B_3020) ) ),
    inference(resolution,[status(thm)],[c_24366,c_2])).

tff(c_24350,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24343,c_64])).

tff(c_24565,plain,(
    ! [A_3051,B_3052,C_3053] : k2_zfmisc_1(k2_zfmisc_1(A_3051,B_3052),C_3053) = k3_zfmisc_1(A_3051,B_3052,C_3053) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24752,plain,(
    ! [C_3070,A_3071,B_3072] :
      ( ~ r1_tarski(C_3070,k3_zfmisc_1(A_3071,B_3072,C_3070))
      | k1_xboole_0 = C_3070 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24565,c_50])).

tff(c_24765,plain,
    ( ~ r1_tarski('#skF_14',k3_zfmisc_1('#skF_12','#skF_13','#skF_14'))
    | k1_xboole_0 = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_24349,c_24752])).

tff(c_24770,plain,(
    ~ r1_tarski('#skF_14',k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(negUnitSimplification,[status(thm)],[c_24350,c_24765])).

tff(c_24774,plain,(
    ~ v1_xboole_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_24370,c_24770])).

tff(c_28141,plain,(
    ! [A_3275,B_3276,C_3277] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_3275,B_3276,C_3277))
      | v1_xboole_0(C_3277)
      | v1_xboole_0(k2_zfmisc_1(A_3275,B_3276)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24565,c_54])).

tff(c_28177,plain,
    ( ~ v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14'))
    | v1_xboole_0('#skF_14')
    | v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24349,c_28141])).

tff(c_28194,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(negUnitSimplification,[status(thm)],[c_27019,c_24774,c_28177])).

tff(c_28209,plain,(
    ~ v1_xboole_0('#skF_13') ),
    inference(resolution,[status(thm)],[c_25689,c_28194])).

tff(c_24342,plain,(
    '#skF_10' != '#skF_13' ),
    inference(splitRight,[status(thm)],[c_12864])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24371,plain,(
    ! [A_3021,B_3022] :
      ( ~ v1_xboole_0(A_3021)
      | r1_tarski(A_3021,B_3022) ) ),
    inference(resolution,[status(thm)],[c_24366,c_2])).

tff(c_24387,plain,(
    ! [A_3025] :
      ( k1_xboole_0 = A_3025
      | ~ v1_xboole_0(A_3025) ) ),
    inference(resolution,[status(thm)],[c_24371,c_52])).

tff(c_24397,plain,(
    ! [A_3026,B_3027] :
      ( k2_zfmisc_1(A_3026,B_3027) = k1_xboole_0
      | ~ v1_xboole_0(B_3027) ) ),
    inference(resolution,[status(thm)],[c_44,c_24387])).

tff(c_24403,plain,(
    ! [A_3026] : k2_zfmisc_1(A_3026,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_24397])).

tff(c_24843,plain,(
    ! [B_3087,D_3088,A_3089] :
      ( ~ v1_xboole_0(B_3087)
      | ~ r2_hidden(D_3088,k2_zfmisc_1(A_3089,B_3087)) ) ),
    inference(resolution,[status(thm)],[c_24824,c_2])).

tff(c_24863,plain,(
    ! [D_3088] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_3088,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24403,c_24843])).

tff(c_24879,plain,(
    ! [D_3090] : ~ r2_hidden(D_3090,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_24863])).

tff(c_24899,plain,(
    ! [B_6] : r1_tarski(k1_xboole_0,B_6) ),
    inference(resolution,[status(thm)],[c_10,c_24879])).

tff(c_35762,plain,(
    ! [A_3517,B_3518,C_3519] :
      ( k2_relat_1(k3_zfmisc_1(A_3517,B_3518,C_3519)) = C_3519
      | k1_xboole_0 = C_3519
      | k2_zfmisc_1(A_3517,B_3518) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24565,c_56])).

tff(c_35798,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) = '#skF_14'
    | k1_xboole_0 = '#skF_14'
    | k2_zfmisc_1('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24349,c_35762])).

tff(c_35805,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) = '#skF_14'
    | k2_zfmisc_1('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_24350,c_35798])).

tff(c_35806,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_35805])).

tff(c_30309,plain,(
    ! [A_3342,B_3343,C_3344] :
      ( ~ r1_tarski(k2_zfmisc_1(A_3342,B_3343),k3_zfmisc_1(A_3342,B_3343,C_3344))
      | k2_zfmisc_1(A_3342,B_3343) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24565,c_52])).

tff(c_30388,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_12','#skF_10'),k3_zfmisc_1('#skF_12','#skF_13','#skF_14'))
    | k2_zfmisc_1('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24349,c_30309])).

tff(c_30812,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_12','#skF_10'),k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_30388])).

tff(c_35807,plain,(
    ~ r1_tarski(k1_xboole_0,k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35806,c_30812])).

tff(c_35811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24899,c_35807])).

tff(c_35813,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_35805])).

tff(c_36414,plain,(
    ! [A_3538,B_3539,C_3540] :
      ( k1_relat_1(k3_zfmisc_1(A_3538,B_3539,C_3540)) = k2_zfmisc_1(A_3538,B_3539)
      | k1_xboole_0 = C_3540
      | k2_zfmisc_1(A_3538,B_3539) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24565,c_58])).

tff(c_36453,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) = k2_zfmisc_1('#skF_12','#skF_10')
    | k1_xboole_0 = '#skF_14'
    | k2_zfmisc_1('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24349,c_36414])).

tff(c_36460,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_12','#skF_13','#skF_14')) = k2_zfmisc_1('#skF_12','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_35813,c_24350,c_36453])).

tff(c_24584,plain,(
    ! [A_3051,B_3052,C_3053] :
      ( k1_relat_1(k3_zfmisc_1(A_3051,B_3052,C_3053)) = k2_zfmisc_1(A_3051,B_3052)
      | k1_xboole_0 = C_3053
      | k2_zfmisc_1(A_3051,B_3052) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24565,c_58])).

tff(c_36464,plain,
    ( k2_zfmisc_1('#skF_12','#skF_10') = k2_zfmisc_1('#skF_12','#skF_13')
    | k1_xboole_0 = '#skF_14'
    | k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36460,c_24584])).

tff(c_36470,plain,
    ( k2_zfmisc_1('#skF_12','#skF_10') = k2_zfmisc_1('#skF_12','#skF_13')
    | k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_24350,c_36464])).

tff(c_36473,plain,(
    k2_zfmisc_1('#skF_12','#skF_13') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36470])).

tff(c_25411,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_57,B_58))
      | v1_xboole_0(k3_zfmisc_1(A_57,B_58,C_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_25389])).

tff(c_28207,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_13')) ),
    inference(resolution,[status(thm)],[c_25411,c_28194])).

tff(c_36474,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36473,c_28207])).

tff(c_36477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36474])).

tff(c_36478,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') = k2_zfmisc_1('#skF_12','#skF_13') ),
    inference(splitRight,[status(thm)],[c_36470])).

tff(c_36635,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_12','#skF_13')) = '#skF_10'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_36478,c_56])).

tff(c_36671,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_12','#skF_13')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_12866,c_66,c_36635])).

tff(c_36845,plain,
    ( '#skF_10' = '#skF_13'
    | k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_36671,c_56])).

tff(c_36851,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(negUnitSimplification,[status(thm)],[c_12866,c_24342,c_36845])).

tff(c_36903,plain,(
    v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36851,c_12])).

tff(c_36906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28209,c_36903])).

tff(c_36907,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30388])).

tff(c_36909,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36907,c_27019])).

tff(c_36912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36909])).

tff(c_36914,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_12','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_26854])).

tff(c_36940,plain,
    ( v1_xboole_0('#skF_10')
    | v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_36914,c_54])).

tff(c_36958,plain,(
    v1_xboole_0('#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_25690,c_36940])).

tff(c_24380,plain,(
    ! [A_3021] :
      ( k1_xboole_0 = A_3021
      | ~ v1_xboole_0(A_3021) ) ),
    inference(resolution,[status(thm)],[c_24371,c_52])).

tff(c_36977,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_36958,c_24380])).

tff(c_36989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12866,c_36977])).

tff(c_36991,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_25673])).

tff(c_37008,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_36991,c_24380])).

tff(c_37019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_37008])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:07:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.14/4.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.41/4.32  
% 10.41/4.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.41/4.32  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_zfmisc_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_14 > #skF_13 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_12
% 10.41/4.32  
% 10.41/4.32  %Foreground sorts:
% 10.41/4.32  
% 10.41/4.32  
% 10.41/4.32  %Background operators:
% 10.41/4.32  
% 10.41/4.32  
% 10.41/4.32  %Foreground operators:
% 10.41/4.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.41/4.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.41/4.32  tff('#skF_11', type, '#skF_11': $i).
% 10.41/4.32  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 10.41/4.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.41/4.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.41/4.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.41/4.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.41/4.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.41/4.32  tff('#skF_10', type, '#skF_10': $i).
% 10.41/4.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.41/4.32  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 10.41/4.32  tff('#skF_14', type, '#skF_14': $i).
% 10.41/4.32  tff('#skF_13', type, '#skF_13': $i).
% 10.41/4.32  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.41/4.32  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 10.41/4.32  tff('#skF_9', type, '#skF_9': $i).
% 10.41/4.32  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 10.41/4.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.41/4.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.41/4.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.41/4.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.41/4.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.41/4.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.41/4.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.41/4.32  tff('#skF_12', type, '#skF_12': $i).
% 10.41/4.32  
% 10.47/4.36  tff(f_116, negated_conjecture, ~(![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_mcart_1)).
% 10.47/4.36  tff(f_101, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 10.47/4.36  tff(f_57, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 10.47/4.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.47/4.36  tff(f_61, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 10.47/4.36  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => ~v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_subset_1)).
% 10.47/4.36  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.47/4.36  tff(f_99, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 10.47/4.36  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.47/4.36  tff(f_78, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 10.47/4.36  tff(f_72, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 10.47/4.36  tff(c_66, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.47/4.36  tff(c_64, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.47/4.36  tff(c_68, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.47/4.36  tff(c_70, plain, (k3_zfmisc_1('#skF_9', '#skF_10', '#skF_11')=k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.47/4.36  tff(c_60, plain, (![A_57, B_58, C_59]: (k2_zfmisc_1(k2_zfmisc_1(A_57, B_58), C_59)=k3_zfmisc_1(A_57, B_58, C_59))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.47/4.36  tff(c_26, plain, (![A_12, B_13, D_39]: (r2_hidden('#skF_7'(A_12, B_13, k2_zfmisc_1(A_12, B_13), D_39), A_12) | ~r2_hidden(D_39, k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.47/4.36  tff(c_1147, plain, (![A_1149, B_1150, D_1151]: (r2_hidden('#skF_7'(A_1149, B_1150, k2_zfmisc_1(A_1149, B_1150), D_1151), A_1149) | ~r2_hidden(D_1151, k2_zfmisc_1(A_1149, B_1150)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.47/4.36  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.47/4.36  tff(c_1606, plain, (![A_1166, D_1167, B_1168]: (~v1_xboole_0(A_1166) | ~r2_hidden(D_1167, k2_zfmisc_1(A_1166, B_1168)))), inference(resolution, [status(thm)], [c_1147, c_2])).
% 10.47/4.36  tff(c_1629, plain, (![A_1166, D_39, B_1168, B_13]: (~v1_xboole_0(A_1166) | ~r2_hidden(D_39, k2_zfmisc_1(k2_zfmisc_1(A_1166, B_1168), B_13)))), inference(resolution, [status(thm)], [c_26, c_1606])).
% 10.47/4.36  tff(c_1920, plain, (![A_1188, D_1189, B_1190, B_1191]: (~v1_xboole_0(A_1188) | ~r2_hidden(D_1189, k3_zfmisc_1(A_1188, B_1190, B_1191)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1629])).
% 10.47/4.36  tff(c_1975, plain, (![D_1189]: (~v1_xboole_0('#skF_9') | ~r2_hidden(D_1189, k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1920])).
% 10.47/4.36  tff(c_1988, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_1975])).
% 10.47/4.36  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.47/4.36  tff(c_950, plain, (![A_1133, B_1134, D_1135]: (r2_hidden('#skF_8'(A_1133, B_1134, k2_zfmisc_1(A_1133, B_1134), D_1135), B_1134) | ~r2_hidden(D_1135, k2_zfmisc_1(A_1133, B_1134)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.47/4.36  tff(c_969, plain, (![B_1134, D_1135, A_1133]: (~v1_xboole_0(B_1134) | ~r2_hidden(D_1135, k2_zfmisc_1(A_1133, B_1134)))), inference(resolution, [status(thm)], [c_950, c_2])).
% 10.47/4.36  tff(c_1163, plain, (![B_1134, D_1151, A_1133, B_1150]: (~v1_xboole_0(B_1134) | ~r2_hidden(D_1151, k2_zfmisc_1(k2_zfmisc_1(A_1133, B_1134), B_1150)))), inference(resolution, [status(thm)], [c_1147, c_969])).
% 10.47/4.36  tff(c_2038, plain, (![B_1195, D_1196, A_1197, B_1198]: (~v1_xboole_0(B_1195) | ~r2_hidden(D_1196, k3_zfmisc_1(A_1197, B_1195, B_1198)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1163])).
% 10.47/4.36  tff(c_2106, plain, (![B_1199, A_1200, B_1201]: (~v1_xboole_0(B_1199) | v1_xboole_0(k3_zfmisc_1(A_1200, B_1199, B_1201)))), inference(resolution, [status(thm)], [c_4, c_2038])).
% 10.47/4.36  tff(c_2140, plain, (~v1_xboole_0('#skF_10') | v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2106])).
% 10.47/4.36  tff(c_2155, plain, (~v1_xboole_0('#skF_10')), inference(splitLeft, [status(thm)], [c_2140])).
% 10.47/4.36  tff(c_197, plain, (![A_89, B_90, C_91]: (k2_zfmisc_1(k2_zfmisc_1(A_89, B_90), C_91)=k3_zfmisc_1(A_89, B_90, C_91))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.47/4.36  tff(c_44, plain, (![A_46, B_47]: (v1_xboole_0(k2_zfmisc_1(A_46, B_47)) | ~v1_xboole_0(B_47))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.47/4.36  tff(c_219, plain, (![A_89, B_90, C_91]: (v1_xboole_0(k3_zfmisc_1(A_89, B_90, C_91)) | ~v1_xboole_0(C_91))), inference(superposition, [status(thm), theory('equality')], [c_197, c_44])).
% 10.47/4.36  tff(c_1675, plain, (![A_1169, B_1170]: (~v1_xboole_0(A_1169) | v1_xboole_0(k2_zfmisc_1(A_1169, B_1170)))), inference(resolution, [status(thm)], [c_4, c_1606])).
% 10.47/4.36  tff(c_2949, plain, (![A_1249, B_1250, C_1251]: (~v1_xboole_0(k2_zfmisc_1(A_1249, B_1250)) | v1_xboole_0(k3_zfmisc_1(A_1249, B_1250, C_1251)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1675])).
% 10.47/4.36  tff(c_2985, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10')) | v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2949])).
% 10.47/4.36  tff(c_3498, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_2985])).
% 10.47/4.36  tff(c_243, plain, (![A_94, B_95, C_96]: (v1_xboole_0(k3_zfmisc_1(A_94, B_95, C_96)) | ~v1_xboole_0(C_96))), inference(superposition, [status(thm), theory('equality')], [c_197, c_44])).
% 10.47/4.36  tff(c_256, plain, (v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')) | ~v1_xboole_0('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_70, c_243])).
% 10.47/4.36  tff(c_262, plain, (~v1_xboole_0('#skF_11')), inference(splitLeft, [status(thm)], [c_256])).
% 10.47/4.36  tff(c_54, plain, (![A_53, B_54]: (~v1_xboole_0(k2_zfmisc_1(A_53, B_54)) | v1_xboole_0(B_54) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.47/4.36  tff(c_5612, plain, (![A_1341, B_1342, C_1343]: (~v1_xboole_0(k3_zfmisc_1(A_1341, B_1342, C_1343)) | v1_xboole_0(C_1343) | v1_xboole_0(k2_zfmisc_1(A_1341, B_1342)))), inference(superposition, [status(thm), theory('equality')], [c_197, c_54])).
% 10.47/4.36  tff(c_5660, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')) | v1_xboole_0('#skF_11') | v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_5612])).
% 10.47/4.36  tff(c_5685, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_3498, c_262, c_5660])).
% 10.47/4.36  tff(c_5701, plain, (~v1_xboole_0('#skF_14')), inference(resolution, [status(thm)], [c_219, c_5685])).
% 10.47/4.36  tff(c_2105, plain, (![B_1195, A_1197, B_1198]: (~v1_xboole_0(B_1195) | v1_xboole_0(k3_zfmisc_1(A_1197, B_1195, B_1198)))), inference(resolution, [status(thm)], [c_4, c_2038])).
% 10.47/4.36  tff(c_5699, plain, (~v1_xboole_0('#skF_13')), inference(resolution, [status(thm)], [c_2105, c_5685])).
% 10.47/4.36  tff(c_1987, plain, (![A_1188, B_1190, B_1191]: (~v1_xboole_0(A_1188) | v1_xboole_0(k3_zfmisc_1(A_1188, B_1190, B_1191)))), inference(resolution, [status(thm)], [c_4, c_1920])).
% 10.47/4.36  tff(c_5700, plain, (~v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_1987, c_5685])).
% 10.47/4.36  tff(c_62, plain, ('#skF_11'!='#skF_14' | '#skF_10'!='#skF_13' | '#skF_9'!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.47/4.36  tff(c_75, plain, ('#skF_9'!='#skF_12'), inference(splitLeft, [status(thm)], [c_62])).
% 10.47/4.36  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.47/4.36  tff(c_412, plain, (![A_116, B_117]: (k2_relat_1(k2_zfmisc_1(A_116, B_117))=B_117 | k1_xboole_0=B_117 | k1_xboole_0=A_116)), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.47/4.36  tff(c_7219, plain, (![A_1407, B_1408, C_1409]: (k2_relat_1(k3_zfmisc_1(A_1407, B_1408, C_1409))=C_1409 | k1_xboole_0=C_1409 | k2_zfmisc_1(A_1407, B_1408)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_412])).
% 10.47/4.36  tff(c_7252, plain, (k2_relat_1(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))='#skF_11' | k1_xboole_0='#skF_11' | k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_70, c_7219])).
% 10.47/4.36  tff(c_7259, plain, (k2_relat_1(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))='#skF_11' | k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_7252])).
% 10.47/4.36  tff(c_7394, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7259])).
% 10.47/4.36  tff(c_7395, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7394, c_3498])).
% 10.47/4.36  tff(c_7398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_7395])).
% 10.47/4.36  tff(c_7399, plain, (k2_relat_1(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))='#skF_11'), inference(splitRight, [status(thm)], [c_7259])).
% 10.47/4.36  tff(c_424, plain, (![A_57, B_58, C_59]: (k2_relat_1(k3_zfmisc_1(A_57, B_58, C_59))=C_59 | k1_xboole_0=C_59 | k2_zfmisc_1(A_57, B_58)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_412])).
% 10.47/4.36  tff(c_7404, plain, ('#skF_11'='#skF_14' | k1_xboole_0='#skF_14' | k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7399, c_424])).
% 10.47/4.36  tff(c_7411, plain, (k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7404])).
% 10.47/4.36  tff(c_1707, plain, (![A_57, B_58, C_59]: (~v1_xboole_0(k2_zfmisc_1(A_57, B_58)) | v1_xboole_0(k3_zfmisc_1(A_57, B_58, C_59)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1675])).
% 10.47/4.36  tff(c_5698, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_13'))), inference(resolution, [status(thm)], [c_1707, c_5685])).
% 10.47/4.36  tff(c_7412, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7411, c_5698])).
% 10.47/4.36  tff(c_7415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_7412])).
% 10.47/4.36  tff(c_7417, plain, (k2_zfmisc_1('#skF_12', '#skF_13')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_7404])).
% 10.47/4.36  tff(c_7416, plain, (k1_xboole_0='#skF_14' | '#skF_11'='#skF_14'), inference(splitRight, [status(thm)], [c_7404])).
% 10.47/4.36  tff(c_7418, plain, ('#skF_11'='#skF_14'), inference(splitLeft, [status(thm)], [c_7416])).
% 10.47/4.36  tff(c_7423, plain, (k1_xboole_0!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_7418, c_64])).
% 10.47/4.36  tff(c_7400, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_7259])).
% 10.47/4.36  tff(c_7422, plain, (k3_zfmisc_1('#skF_9', '#skF_10', '#skF_14')=k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_7418, c_70])).
% 10.47/4.36  tff(c_322, plain, (![A_105, B_106]: (k1_relat_1(k2_zfmisc_1(A_105, B_106))=A_105 | k1_xboole_0=B_106 | k1_xboole_0=A_105)), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.47/4.36  tff(c_12302, plain, (![A_1564, B_1565, C_1566]: (k1_relat_1(k3_zfmisc_1(A_1564, B_1565, C_1566))=k2_zfmisc_1(A_1564, B_1565) | k1_xboole_0=C_1566 | k2_zfmisc_1(A_1564, B_1565)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_322])).
% 10.47/4.36  tff(c_12317, plain, (k1_relat_1(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))=k2_zfmisc_1('#skF_9', '#skF_10') | k1_xboole_0='#skF_14' | k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7422, c_12302])).
% 10.47/4.36  tff(c_12344, plain, (k1_relat_1(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_7400, c_7423, c_12317])).
% 10.47/4.36  tff(c_331, plain, (![A_57, B_58, C_59]: (k1_relat_1(k3_zfmisc_1(A_57, B_58, C_59))=k2_zfmisc_1(A_57, B_58) | k1_xboole_0=C_59 | k2_zfmisc_1(A_57, B_58)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_322])).
% 10.47/4.36  tff(c_12352, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k2_zfmisc_1('#skF_12', '#skF_13') | k1_xboole_0='#skF_14' | k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12344, c_331])).
% 10.47/4.36  tff(c_12358, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k2_zfmisc_1('#skF_12', '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_7417, c_7423, c_12352])).
% 10.47/4.36  tff(c_58, plain, (![A_55, B_56]: (k1_relat_1(k2_zfmisc_1(A_55, B_56))=A_55 | k1_xboole_0=B_56 | k1_xboole_0=A_55)), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.47/4.36  tff(c_12512, plain, (k1_relat_1(k2_zfmisc_1('#skF_12', '#skF_13'))='#skF_9' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_12358, c_58])).
% 10.47/4.36  tff(c_12545, plain, (k1_relat_1(k2_zfmisc_1('#skF_12', '#skF_13'))='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_68, c_66, c_12512])).
% 10.47/4.36  tff(c_12565, plain, ('#skF_9'='#skF_12' | k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_12545, c_58])).
% 10.47/4.36  tff(c_12571, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12'), inference(negUnitSimplification, [status(thm)], [c_75, c_12565])).
% 10.47/4.36  tff(c_12574, plain, (k1_xboole_0='#skF_12'), inference(splitLeft, [status(thm)], [c_12571])).
% 10.47/4.36  tff(c_12621, plain, (v1_xboole_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_12574, c_12])).
% 10.47/4.36  tff(c_12625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5700, c_12621])).
% 10.47/4.36  tff(c_12626, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_12571])).
% 10.47/4.36  tff(c_12675, plain, (v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_12626, c_12])).
% 10.47/4.36  tff(c_12679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5699, c_12675])).
% 10.47/4.36  tff(c_12680, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_7416])).
% 10.47/4.36  tff(c_12722, plain, (v1_xboole_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_12680, c_12])).
% 10.47/4.36  tff(c_12727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5701, c_12722])).
% 10.47/4.36  tff(c_12729, plain, (v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_2985])).
% 10.47/4.36  tff(c_12762, plain, (v1_xboole_0('#skF_10') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_12729, c_54])).
% 10.47/4.36  tff(c_12782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1988, c_2155, c_12762])).
% 10.47/4.36  tff(c_12784, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_2140])).
% 10.47/4.36  tff(c_94, plain, (![A_72, B_73]: (r2_hidden('#skF_2'(A_72, B_73), A_72) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.47/4.36  tff(c_104, plain, (![A_76, B_77]: (~v1_xboole_0(A_76) | r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_94, c_2])).
% 10.47/4.36  tff(c_50, plain, (![A_51, B_52]: (~r1_tarski(A_51, k2_zfmisc_1(B_52, A_51)) | k1_xboole_0=A_51)), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.47/4.36  tff(c_116, plain, (![A_76]: (k1_xboole_0=A_76 | ~v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_104, c_50])).
% 10.47/4.36  tff(c_12803, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_12784, c_116])).
% 10.47/4.36  tff(c_12815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_12803])).
% 10.47/4.36  tff(c_12817, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_1975])).
% 10.47/4.36  tff(c_12836, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_12817, c_116])).
% 10.47/4.36  tff(c_12848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_12836])).
% 10.47/4.36  tff(c_12850, plain, (v1_xboole_0('#skF_11')), inference(splitRight, [status(thm)], [c_256])).
% 10.47/4.36  tff(c_12857, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_12850, c_116])).
% 10.47/4.36  tff(c_12863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_12857])).
% 10.47/4.36  tff(c_12865, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_62])).
% 10.47/4.36  tff(c_12866, plain, (k1_xboole_0!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_12865, c_68])).
% 10.47/4.36  tff(c_12879, plain, (k3_zfmisc_1('#skF_12', '#skF_10', '#skF_11')=k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_12865, c_70])).
% 10.47/4.36  tff(c_13812, plain, (![A_2597, B_2598, D_2599]: (r2_hidden('#skF_8'(A_2597, B_2598, k2_zfmisc_1(A_2597, B_2598), D_2599), B_2598) | ~r2_hidden(D_2599, k2_zfmisc_1(A_2597, B_2598)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.47/4.36  tff(c_14200, plain, (![B_2616, D_2617, A_2618]: (~v1_xboole_0(B_2616) | ~r2_hidden(D_2617, k2_zfmisc_1(A_2618, B_2616)))), inference(resolution, [status(thm)], [c_13812, c_2])).
% 10.47/4.36  tff(c_14227, plain, (![B_2616, D_39, A_2618, B_13]: (~v1_xboole_0(B_2616) | ~r2_hidden(D_39, k2_zfmisc_1(k2_zfmisc_1(A_2618, B_2616), B_13)))), inference(resolution, [status(thm)], [c_26, c_14200])).
% 10.47/4.36  tff(c_14693, plain, (![B_2653, D_2654, A_2655, B_2656]: (~v1_xboole_0(B_2653) | ~r2_hidden(D_2654, k3_zfmisc_1(A_2655, B_2653, B_2656)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_14227])).
% 10.47/4.36  tff(c_14762, plain, (![B_2662, A_2663, B_2664]: (~v1_xboole_0(B_2662) | v1_xboole_0(k3_zfmisc_1(A_2663, B_2662, B_2664)))), inference(resolution, [status(thm)], [c_4, c_14693])).
% 10.47/4.36  tff(c_14796, plain, (~v1_xboole_0('#skF_10') | v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_12879, c_14762])).
% 10.47/4.36  tff(c_14811, plain, (~v1_xboole_0('#skF_10')), inference(splitLeft, [status(thm)], [c_14796])).
% 10.47/4.36  tff(c_13083, plain, (![A_1609, B_1610, C_1611]: (k2_zfmisc_1(k2_zfmisc_1(A_1609, B_1610), C_1611)=k3_zfmisc_1(A_1609, B_1610, C_1611))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.47/4.36  tff(c_13118, plain, (![A_1609, B_1610, C_1611]: (v1_xboole_0(k3_zfmisc_1(A_1609, B_1610, C_1611)) | ~v1_xboole_0(C_1611))), inference(superposition, [status(thm), theory('equality')], [c_13083, c_44])).
% 10.47/4.36  tff(c_13647, plain, (![A_2587, B_2588, D_2589]: (r2_hidden('#skF_7'(A_2587, B_2588, k2_zfmisc_1(A_2587, B_2588), D_2589), A_2587) | ~r2_hidden(D_2589, k2_zfmisc_1(A_2587, B_2588)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.47/4.36  tff(c_13669, plain, (![A_2590, D_2591, B_2592]: (~v1_xboole_0(A_2590) | ~r2_hidden(D_2591, k2_zfmisc_1(A_2590, B_2592)))), inference(resolution, [status(thm)], [c_13647, c_2])).
% 10.47/4.36  tff(c_14098, plain, (![A_2609, B_2610]: (~v1_xboole_0(A_2609) | v1_xboole_0(k2_zfmisc_1(A_2609, B_2610)))), inference(resolution, [status(thm)], [c_4, c_13669])).
% 10.47/4.36  tff(c_15853, plain, (![A_2724, B_2725, C_2726]: (~v1_xboole_0(k2_zfmisc_1(A_2724, B_2725)) | v1_xboole_0(k3_zfmisc_1(A_2724, B_2725, C_2726)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_14098])).
% 10.47/4.36  tff(c_15889, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10')) | v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_12879, c_15853])).
% 10.47/4.36  tff(c_16597, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10'))), inference(splitLeft, [status(thm)], [c_15889])).
% 10.47/4.36  tff(c_13149, plain, (![A_1614, B_1615, C_1616]: (v1_xboole_0(k3_zfmisc_1(A_1614, B_1615, C_1616)) | ~v1_xboole_0(C_1616))), inference(superposition, [status(thm), theory('equality')], [c_13083, c_44])).
% 10.47/4.36  tff(c_13164, plain, (v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')) | ~v1_xboole_0('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_12879, c_13149])).
% 10.47/4.36  tff(c_13171, plain, (~v1_xboole_0('#skF_11')), inference(splitLeft, [status(thm)], [c_13164])).
% 10.47/4.36  tff(c_18047, plain, (![A_2794, B_2795, C_2796]: (~v1_xboole_0(k3_zfmisc_1(A_2794, B_2795, C_2796)) | v1_xboole_0(C_2796) | v1_xboole_0(k2_zfmisc_1(A_2794, B_2795)))), inference(superposition, [status(thm), theory('equality')], [c_13083, c_54])).
% 10.47/4.36  tff(c_18089, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')) | v1_xboole_0('#skF_11') | v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_12879, c_18047])).
% 10.47/4.36  tff(c_18110, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_16597, c_13171, c_18089])).
% 10.47/4.36  tff(c_18126, plain, (~v1_xboole_0('#skF_14')), inference(resolution, [status(thm)], [c_13118, c_18110])).
% 10.47/4.36  tff(c_12864, plain, ('#skF_10'!='#skF_13' | '#skF_11'!='#skF_14'), inference(splitRight, [status(thm)], [c_62])).
% 10.47/4.36  tff(c_12871, plain, ('#skF_11'!='#skF_14'), inference(splitLeft, [status(thm)], [c_12864])).
% 10.47/4.36  tff(c_12890, plain, (![A_1581, B_1582]: (r2_hidden('#skF_2'(A_1581, B_1582), A_1581) | r1_tarski(A_1581, B_1582))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.47/4.36  tff(c_12901, plain, (![A_1583, B_1584]: (~v1_xboole_0(A_1583) | r1_tarski(A_1583, B_1584))), inference(resolution, [status(thm)], [c_12890, c_2])).
% 10.47/4.36  tff(c_52, plain, (![A_51, B_52]: (~r1_tarski(A_51, k2_zfmisc_1(A_51, B_52)) | k1_xboole_0=A_51)), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.47/4.36  tff(c_12912, plain, (![A_1585]: (k1_xboole_0=A_1585 | ~v1_xboole_0(A_1585))), inference(resolution, [status(thm)], [c_12901, c_52])).
% 10.47/4.36  tff(c_12922, plain, (![A_1586, B_1587]: (k2_zfmisc_1(A_1586, B_1587)=k1_xboole_0 | ~v1_xboole_0(B_1587))), inference(resolution, [status(thm)], [c_44, c_12912])).
% 10.47/4.36  tff(c_12928, plain, (![A_1586]: (k2_zfmisc_1(A_1586, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_12922])).
% 10.47/4.36  tff(c_12900, plain, (![A_1581, B_1582]: (~v1_xboole_0(A_1581) | r1_tarski(A_1581, B_1582))), inference(resolution, [status(thm)], [c_12890, c_2])).
% 10.47/4.36  tff(c_13295, plain, (![A_1635, B_1636, C_1637]: (~r1_tarski(k2_zfmisc_1(A_1635, B_1636), k2_zfmisc_1(A_1635, C_1637)) | r1_tarski(B_1636, C_1637) | k1_xboole_0=A_1635)), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.47/4.36  tff(c_13326, plain, (![B_1638, C_1639, A_1640]: (r1_tarski(B_1638, C_1639) | k1_xboole_0=A_1640 | ~v1_xboole_0(k2_zfmisc_1(A_1640, B_1638)))), inference(resolution, [status(thm)], [c_12900, c_13295])).
% 10.47/4.36  tff(c_13332, plain, (![C_1639, A_1586]: (r1_tarski(k1_xboole_0, C_1639) | k1_xboole_0=A_1586 | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12928, c_13326])).
% 10.47/4.36  tff(c_13338, plain, (![C_1639, A_1586]: (r1_tarski(k1_xboole_0, C_1639) | k1_xboole_0=A_1586)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_13332])).
% 10.47/4.36  tff(c_13424, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_13338])).
% 10.47/4.36  tff(c_13425, plain, (v1_xboole_0('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_13424, c_12])).
% 10.47/4.36  tff(c_13454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13171, c_13425])).
% 10.47/4.36  tff(c_13455, plain, (![C_1639]: (r1_tarski(k1_xboole_0, C_1639))), inference(splitRight, [status(thm)], [c_13338])).
% 10.47/4.36  tff(c_56, plain, (![A_55, B_56]: (k2_relat_1(k2_zfmisc_1(A_55, B_56))=B_56 | k1_xboole_0=B_56 | k1_xboole_0=A_55)), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.47/4.36  tff(c_24015, plain, (![A_3008, B_3009, C_3010]: (k2_relat_1(k3_zfmisc_1(A_3008, B_3009, C_3010))=C_3010 | k1_xboole_0=C_3010 | k2_zfmisc_1(A_3008, B_3009)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13083, c_56])).
% 10.47/4.36  tff(c_24051, plain, (k2_relat_1(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))='#skF_11' | k1_xboole_0='#skF_11' | k2_zfmisc_1('#skF_12', '#skF_10')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12879, c_24015])).
% 10.47/4.36  tff(c_24058, plain, (k2_relat_1(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))='#skF_11' | k2_zfmisc_1('#skF_12', '#skF_10')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_24051])).
% 10.47/4.36  tff(c_24059, plain, (k2_zfmisc_1('#skF_12', '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24058])).
% 10.47/4.36  tff(c_20000, plain, (![A_2868, B_2869, C_2870]: (~r1_tarski(k2_zfmisc_1(A_2868, B_2869), k3_zfmisc_1(A_2868, B_2869, C_2870)) | k2_zfmisc_1(A_2868, B_2869)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13083, c_52])).
% 10.47/4.36  tff(c_20079, plain, (~r1_tarski(k2_zfmisc_1('#skF_12', '#skF_10'), k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')) | k2_zfmisc_1('#skF_12', '#skF_10')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12879, c_20000])).
% 10.47/4.36  tff(c_20455, plain, (~r1_tarski(k2_zfmisc_1('#skF_12', '#skF_10'), k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(splitLeft, [status(thm)], [c_20079])).
% 10.47/4.36  tff(c_24060, plain, (~r1_tarski(k1_xboole_0, k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_24059, c_20455])).
% 10.47/4.36  tff(c_24064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13455, c_24060])).
% 10.47/4.36  tff(c_24065, plain, (k2_relat_1(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))='#skF_11'), inference(splitRight, [status(thm)], [c_24058])).
% 10.47/4.36  tff(c_13102, plain, (![A_1609, B_1610, C_1611]: (k2_relat_1(k3_zfmisc_1(A_1609, B_1610, C_1611))=C_1611 | k1_xboole_0=C_1611 | k2_zfmisc_1(A_1609, B_1610)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13083, c_56])).
% 10.47/4.36  tff(c_24070, plain, ('#skF_11'='#skF_14' | k1_xboole_0='#skF_14' | k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24065, c_13102])).
% 10.47/4.36  tff(c_24076, plain, (k1_xboole_0='#skF_14' | k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_12871, c_24070])).
% 10.47/4.36  tff(c_24079, plain, (k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24076])).
% 10.47/4.36  tff(c_14127, plain, (![A_57, B_58, C_59]: (~v1_xboole_0(k2_zfmisc_1(A_57, B_58)) | v1_xboole_0(k3_zfmisc_1(A_57, B_58, C_59)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_14098])).
% 10.47/4.36  tff(c_18123, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_13'))), inference(resolution, [status(thm)], [c_14127, c_18110])).
% 10.47/4.36  tff(c_24080, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24079, c_18123])).
% 10.47/4.36  tff(c_24083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_24080])).
% 10.47/4.36  tff(c_24084, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_24076])).
% 10.47/4.36  tff(c_24129, plain, (v1_xboole_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_24084, c_12])).
% 10.47/4.36  tff(c_24133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18126, c_24129])).
% 10.47/4.36  tff(c_24134, plain, (k2_zfmisc_1('#skF_12', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_20079])).
% 10.47/4.36  tff(c_24136, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24134, c_16597])).
% 10.47/4.36  tff(c_24139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_24136])).
% 10.47/4.36  tff(c_24141, plain, (v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10'))), inference(splitRight, [status(thm)], [c_15889])).
% 10.47/4.36  tff(c_24175, plain, (v1_xboole_0('#skF_10') | v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_24141, c_54])).
% 10.47/4.36  tff(c_24197, plain, (v1_xboole_0('#skF_12')), inference(negUnitSimplification, [status(thm)], [c_14811, c_24175])).
% 10.47/4.36  tff(c_12910, plain, (![A_1583]: (k1_xboole_0=A_1583 | ~v1_xboole_0(A_1583))), inference(resolution, [status(thm)], [c_12901, c_52])).
% 10.47/4.36  tff(c_24275, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_24197, c_12910])).
% 10.47/4.36  tff(c_24290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12866, c_24275])).
% 10.47/4.36  tff(c_24292, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_14796])).
% 10.47/4.36  tff(c_24311, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_24292, c_12910])).
% 10.47/4.36  tff(c_24323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_24311])).
% 10.47/4.36  tff(c_24325, plain, (v1_xboole_0('#skF_11')), inference(splitRight, [status(thm)], [c_13164])).
% 10.47/4.36  tff(c_24334, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_24325, c_12910])).
% 10.47/4.36  tff(c_24341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_24334])).
% 10.47/4.36  tff(c_24343, plain, ('#skF_11'='#skF_14'), inference(splitRight, [status(thm)], [c_12864])).
% 10.47/4.36  tff(c_24344, plain, (k3_zfmisc_1('#skF_12', '#skF_10', '#skF_11')=k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_12865, c_70])).
% 10.47/4.36  tff(c_24349, plain, (k3_zfmisc_1('#skF_12', '#skF_10', '#skF_14')=k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_24343, c_24344])).
% 10.47/4.36  tff(c_25016, plain, (![A_3096, B_3097, D_3098]: (r2_hidden('#skF_7'(A_3096, B_3097, k2_zfmisc_1(A_3096, B_3097), D_3098), A_3096) | ~r2_hidden(D_3098, k2_zfmisc_1(A_3096, B_3097)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.47/4.36  tff(c_24824, plain, (![A_3084, B_3085, D_3086]: (r2_hidden('#skF_8'(A_3084, B_3085, k2_zfmisc_1(A_3084, B_3085), D_3086), B_3085) | ~r2_hidden(D_3086, k2_zfmisc_1(A_3084, B_3085)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.47/4.36  tff(c_24840, plain, (![B_3085, D_3086, A_3084]: (~v1_xboole_0(B_3085) | ~r2_hidden(D_3086, k2_zfmisc_1(A_3084, B_3085)))), inference(resolution, [status(thm)], [c_24824, c_2])).
% 10.47/4.36  tff(c_25024, plain, (![B_3085, D_3098, A_3084, B_3097]: (~v1_xboole_0(B_3085) | ~r2_hidden(D_3098, k2_zfmisc_1(k2_zfmisc_1(A_3084, B_3085), B_3097)))), inference(resolution, [status(thm)], [c_25016, c_24840])).
% 10.47/4.36  tff(c_25625, plain, (![B_3135, D_3136, A_3137, B_3138]: (~v1_xboole_0(B_3135) | ~r2_hidden(D_3136, k3_zfmisc_1(A_3137, B_3135, B_3138)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_25024])).
% 10.47/4.36  tff(c_25673, plain, (![D_3136]: (~v1_xboole_0('#skF_10') | ~r2_hidden(D_3136, k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_24349, c_25625])).
% 10.47/4.36  tff(c_25690, plain, (~v1_xboole_0('#skF_10')), inference(splitLeft, [status(thm)], [c_25673])).
% 10.47/4.36  tff(c_25689, plain, (![B_3135, A_3137, B_3138]: (~v1_xboole_0(B_3135) | v1_xboole_0(k3_zfmisc_1(A_3137, B_3135, B_3138)))), inference(resolution, [status(thm)], [c_4, c_25625])).
% 10.47/4.36  tff(c_25329, plain, (![A_3113, D_3114, B_3115]: (~v1_xboole_0(A_3113) | ~r2_hidden(D_3114, k2_zfmisc_1(A_3113, B_3115)))), inference(resolution, [status(thm)], [c_25016, c_2])).
% 10.47/4.36  tff(c_25389, plain, (![A_3116, B_3117]: (~v1_xboole_0(A_3116) | v1_xboole_0(k2_zfmisc_1(A_3116, B_3117)))), inference(resolution, [status(thm)], [c_4, c_25329])).
% 10.47/4.36  tff(c_26823, plain, (![A_3221, B_3222, C_3223]: (~v1_xboole_0(k2_zfmisc_1(A_3221, B_3222)) | v1_xboole_0(k3_zfmisc_1(A_3221, B_3222, C_3223)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_25389])).
% 10.47/4.36  tff(c_26854, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10')) | v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_24349, c_26823])).
% 10.47/4.36  tff(c_27019, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10'))), inference(splitLeft, [status(thm)], [c_26854])).
% 10.47/4.36  tff(c_24366, plain, (![A_3019, B_3020]: (r2_hidden('#skF_2'(A_3019, B_3020), A_3019) | r1_tarski(A_3019, B_3020))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.47/4.36  tff(c_24370, plain, (![A_3019, B_3020]: (~v1_xboole_0(A_3019) | r1_tarski(A_3019, B_3020))), inference(resolution, [status(thm)], [c_24366, c_2])).
% 10.47/4.36  tff(c_24350, plain, (k1_xboole_0!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_24343, c_64])).
% 10.47/4.36  tff(c_24565, plain, (![A_3051, B_3052, C_3053]: (k2_zfmisc_1(k2_zfmisc_1(A_3051, B_3052), C_3053)=k3_zfmisc_1(A_3051, B_3052, C_3053))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.47/4.36  tff(c_24752, plain, (![C_3070, A_3071, B_3072]: (~r1_tarski(C_3070, k3_zfmisc_1(A_3071, B_3072, C_3070)) | k1_xboole_0=C_3070)), inference(superposition, [status(thm), theory('equality')], [c_24565, c_50])).
% 10.47/4.36  tff(c_24765, plain, (~r1_tarski('#skF_14', k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')) | k1_xboole_0='#skF_14'), inference(superposition, [status(thm), theory('equality')], [c_24349, c_24752])).
% 10.47/4.36  tff(c_24770, plain, (~r1_tarski('#skF_14', k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_24350, c_24765])).
% 10.47/4.36  tff(c_24774, plain, (~v1_xboole_0('#skF_14')), inference(resolution, [status(thm)], [c_24370, c_24770])).
% 10.47/4.36  tff(c_28141, plain, (![A_3275, B_3276, C_3277]: (~v1_xboole_0(k3_zfmisc_1(A_3275, B_3276, C_3277)) | v1_xboole_0(C_3277) | v1_xboole_0(k2_zfmisc_1(A_3275, B_3276)))), inference(superposition, [status(thm), theory('equality')], [c_24565, c_54])).
% 10.47/4.36  tff(c_28177, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')) | v1_xboole_0('#skF_14') | v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_24349, c_28141])).
% 10.47/4.36  tff(c_28194, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_27019, c_24774, c_28177])).
% 10.47/4.36  tff(c_28209, plain, (~v1_xboole_0('#skF_13')), inference(resolution, [status(thm)], [c_25689, c_28194])).
% 10.47/4.36  tff(c_24342, plain, ('#skF_10'!='#skF_13'), inference(splitRight, [status(thm)], [c_12864])).
% 10.47/4.36  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.47/4.36  tff(c_24371, plain, (![A_3021, B_3022]: (~v1_xboole_0(A_3021) | r1_tarski(A_3021, B_3022))), inference(resolution, [status(thm)], [c_24366, c_2])).
% 10.47/4.36  tff(c_24387, plain, (![A_3025]: (k1_xboole_0=A_3025 | ~v1_xboole_0(A_3025))), inference(resolution, [status(thm)], [c_24371, c_52])).
% 10.47/4.36  tff(c_24397, plain, (![A_3026, B_3027]: (k2_zfmisc_1(A_3026, B_3027)=k1_xboole_0 | ~v1_xboole_0(B_3027))), inference(resolution, [status(thm)], [c_44, c_24387])).
% 10.47/4.36  tff(c_24403, plain, (![A_3026]: (k2_zfmisc_1(A_3026, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_24397])).
% 10.47/4.36  tff(c_24843, plain, (![B_3087, D_3088, A_3089]: (~v1_xboole_0(B_3087) | ~r2_hidden(D_3088, k2_zfmisc_1(A_3089, B_3087)))), inference(resolution, [status(thm)], [c_24824, c_2])).
% 10.47/4.36  tff(c_24863, plain, (![D_3088]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(D_3088, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24403, c_24843])).
% 10.47/4.36  tff(c_24879, plain, (![D_3090]: (~r2_hidden(D_3090, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_24863])).
% 10.47/4.36  tff(c_24899, plain, (![B_6]: (r1_tarski(k1_xboole_0, B_6))), inference(resolution, [status(thm)], [c_10, c_24879])).
% 10.47/4.36  tff(c_35762, plain, (![A_3517, B_3518, C_3519]: (k2_relat_1(k3_zfmisc_1(A_3517, B_3518, C_3519))=C_3519 | k1_xboole_0=C_3519 | k2_zfmisc_1(A_3517, B_3518)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24565, c_56])).
% 10.47/4.36  tff(c_35798, plain, (k2_relat_1(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))='#skF_14' | k1_xboole_0='#skF_14' | k2_zfmisc_1('#skF_12', '#skF_10')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24349, c_35762])).
% 10.47/4.36  tff(c_35805, plain, (k2_relat_1(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))='#skF_14' | k2_zfmisc_1('#skF_12', '#skF_10')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_24350, c_35798])).
% 10.47/4.36  tff(c_35806, plain, (k2_zfmisc_1('#skF_12', '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_35805])).
% 10.47/4.36  tff(c_30309, plain, (![A_3342, B_3343, C_3344]: (~r1_tarski(k2_zfmisc_1(A_3342, B_3343), k3_zfmisc_1(A_3342, B_3343, C_3344)) | k2_zfmisc_1(A_3342, B_3343)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24565, c_52])).
% 10.47/4.36  tff(c_30388, plain, (~r1_tarski(k2_zfmisc_1('#skF_12', '#skF_10'), k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14')) | k2_zfmisc_1('#skF_12', '#skF_10')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24349, c_30309])).
% 10.47/4.36  tff(c_30812, plain, (~r1_tarski(k2_zfmisc_1('#skF_12', '#skF_10'), k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(splitLeft, [status(thm)], [c_30388])).
% 10.47/4.36  tff(c_35807, plain, (~r1_tarski(k1_xboole_0, k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_35806, c_30812])).
% 10.47/4.36  tff(c_35811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24899, c_35807])).
% 10.47/4.36  tff(c_35813, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_35805])).
% 10.47/4.36  tff(c_36414, plain, (![A_3538, B_3539, C_3540]: (k1_relat_1(k3_zfmisc_1(A_3538, B_3539, C_3540))=k2_zfmisc_1(A_3538, B_3539) | k1_xboole_0=C_3540 | k2_zfmisc_1(A_3538, B_3539)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24565, c_58])).
% 10.47/4.36  tff(c_36453, plain, (k1_relat_1(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))=k2_zfmisc_1('#skF_12', '#skF_10') | k1_xboole_0='#skF_14' | k2_zfmisc_1('#skF_12', '#skF_10')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24349, c_36414])).
% 10.47/4.36  tff(c_36460, plain, (k1_relat_1(k3_zfmisc_1('#skF_12', '#skF_13', '#skF_14'))=k2_zfmisc_1('#skF_12', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_35813, c_24350, c_36453])).
% 10.47/4.36  tff(c_24584, plain, (![A_3051, B_3052, C_3053]: (k1_relat_1(k3_zfmisc_1(A_3051, B_3052, C_3053))=k2_zfmisc_1(A_3051, B_3052) | k1_xboole_0=C_3053 | k2_zfmisc_1(A_3051, B_3052)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24565, c_58])).
% 10.47/4.36  tff(c_36464, plain, (k2_zfmisc_1('#skF_12', '#skF_10')=k2_zfmisc_1('#skF_12', '#skF_13') | k1_xboole_0='#skF_14' | k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_36460, c_24584])).
% 10.47/4.36  tff(c_36470, plain, (k2_zfmisc_1('#skF_12', '#skF_10')=k2_zfmisc_1('#skF_12', '#skF_13') | k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_24350, c_36464])).
% 10.47/4.36  tff(c_36473, plain, (k2_zfmisc_1('#skF_12', '#skF_13')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36470])).
% 10.47/4.36  tff(c_25411, plain, (![A_57, B_58, C_59]: (~v1_xboole_0(k2_zfmisc_1(A_57, B_58)) | v1_xboole_0(k3_zfmisc_1(A_57, B_58, C_59)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_25389])).
% 10.47/4.36  tff(c_28207, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_13'))), inference(resolution, [status(thm)], [c_25411, c_28194])).
% 10.47/4.36  tff(c_36474, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36473, c_28207])).
% 10.47/4.36  tff(c_36477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_36474])).
% 10.47/4.36  tff(c_36478, plain, (k2_zfmisc_1('#skF_12', '#skF_10')=k2_zfmisc_1('#skF_12', '#skF_13')), inference(splitRight, [status(thm)], [c_36470])).
% 10.47/4.36  tff(c_36635, plain, (k2_relat_1(k2_zfmisc_1('#skF_12', '#skF_13'))='#skF_10' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_36478, c_56])).
% 10.47/4.36  tff(c_36671, plain, (k2_relat_1(k2_zfmisc_1('#skF_12', '#skF_13'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_12866, c_66, c_36635])).
% 10.47/4.36  tff(c_36845, plain, ('#skF_10'='#skF_13' | k1_xboole_0='#skF_13' | k1_xboole_0='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_36671, c_56])).
% 10.47/4.36  tff(c_36851, plain, (k1_xboole_0='#skF_13'), inference(negUnitSimplification, [status(thm)], [c_12866, c_24342, c_36845])).
% 10.47/4.36  tff(c_36903, plain, (v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_36851, c_12])).
% 10.47/4.36  tff(c_36906, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28209, c_36903])).
% 10.47/4.36  tff(c_36907, plain, (k2_zfmisc_1('#skF_12', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_30388])).
% 10.47/4.36  tff(c_36909, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36907, c_27019])).
% 10.47/4.36  tff(c_36912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_36909])).
% 10.47/4.36  tff(c_36914, plain, (v1_xboole_0(k2_zfmisc_1('#skF_12', '#skF_10'))), inference(splitRight, [status(thm)], [c_26854])).
% 10.47/4.36  tff(c_36940, plain, (v1_xboole_0('#skF_10') | v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_36914, c_54])).
% 10.47/4.36  tff(c_36958, plain, (v1_xboole_0('#skF_12')), inference(negUnitSimplification, [status(thm)], [c_25690, c_36940])).
% 10.47/4.36  tff(c_24380, plain, (![A_3021]: (k1_xboole_0=A_3021 | ~v1_xboole_0(A_3021))), inference(resolution, [status(thm)], [c_24371, c_52])).
% 10.47/4.36  tff(c_36977, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_36958, c_24380])).
% 10.47/4.36  tff(c_36989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12866, c_36977])).
% 10.47/4.36  tff(c_36991, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_25673])).
% 10.47/4.36  tff(c_37008, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_36991, c_24380])).
% 10.47/4.36  tff(c_37019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_37008])).
% 10.47/4.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.47/4.36  
% 10.47/4.36  Inference rules
% 10.47/4.36  ----------------------
% 10.47/4.36  #Ref     : 0
% 10.47/4.36  #Sup     : 9205
% 10.47/4.36  #Fact    : 0
% 10.47/4.36  #Define  : 0
% 10.47/4.36  #Split   : 26
% 10.47/4.36  #Chain   : 0
% 10.47/4.36  #Close   : 0
% 10.47/4.36  
% 10.47/4.36  Ordering : KBO
% 10.47/4.36  
% 10.47/4.36  Simplification rules
% 10.47/4.36  ----------------------
% 10.47/4.36  #Subsume      : 3352
% 10.47/4.36  #Demod        : 4868
% 10.47/4.36  #Tautology    : 3100
% 10.47/4.36  #SimpNegUnit  : 118
% 10.47/4.36  #BackRed      : 279
% 10.47/4.36  
% 10.47/4.36  #Partial instantiations: 348
% 10.47/4.36  #Strategies tried      : 1
% 10.47/4.36  
% 10.47/4.36  Timing (in seconds)
% 10.47/4.36  ----------------------
% 10.47/4.36  Preprocessing        : 0.32
% 10.47/4.36  Parsing              : 0.16
% 10.47/4.36  CNF conversion       : 0.03
% 10.47/4.36  Main loop            : 3.20
% 10.47/4.36  Inferencing          : 0.92
% 10.47/4.36  Reduction            : 0.87
% 10.47/4.36  Demodulation         : 0.60
% 10.47/4.36  BG Simplification    : 0.10
% 10.47/4.36  Subsumption          : 1.09
% 10.47/4.36  Abstraction          : 0.14
% 10.47/4.36  MUC search           : 0.00
% 10.47/4.36  Cooper               : 0.00
% 10.47/4.36  Total                : 3.62
% 10.47/4.36  Index Insertion      : 0.00
% 10.47/4.36  Index Deletion       : 0.00
% 10.47/4.36  Index Matching       : 0.00
% 10.47/4.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
