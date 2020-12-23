%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1645+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:11 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 203 expanded)
%              Number of leaves         :   42 (  96 expanded)
%              Depth                    :    9
%              Number of atoms          :  159 ( 727 expanded)
%              Number of equality atoms :   32 ( 151 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > v5_relat_1 > v4_relat_1 > v2_waybel_0 > v1_waybel_0 > v1_subset_1 > v13_waybel_0 > v12_waybel_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k4_waybel_0 > k3_waybel_0 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_2 > #skF_1 > #skF_9 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_waybel_0,type,(
    k3_waybel_0: ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_waybel_0,type,(
    k4_waybel_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( l1_orders_2(B)
           => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( C = D
                       => ( ( v12_waybel_0(C,A)
                           => v12_waybel_0(D,B) )
                          & ( v13_waybel_0(C,A)
                           => v13_waybel_0(D,B) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_0)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( g1_orders_2(u1_struct_0(A),u1_orders_2(A)) = g1_orders_2(u1_struct_0(B),u1_orders_2(B))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( C = D
                     => ( k3_waybel_0(A,C) = k3_waybel_0(B,D)
                        & k4_waybel_0(A,C) = k4_waybel_0(B,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_0)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> r1_tarski(k4_waybel_0(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_0)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v12_waybel_0(B,A)
          <=> r1_tarski(k3_waybel_0(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_0)).

tff(c_60,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_72,plain,
    ( ~ v12_waybel_0('#skF_10','#skF_8')
    | ~ v13_waybel_0('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_82,plain,
    ( ~ v12_waybel_0('#skF_9','#skF_8')
    | ~ v13_waybel_0('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_72])).

tff(c_136,plain,(
    ~ v13_waybel_0('#skF_9','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_68,plain,(
    l1_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_62,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_79,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62])).

tff(c_70,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_66,plain,(
    g1_orders_2(u1_struct_0('#skF_7'),u1_orders_2('#skF_7')) = g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_64,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_443,plain,(
    ! [B_105,D_106,A_107] :
      ( k4_waybel_0(B_105,D_106) = k4_waybel_0(A_107,D_106)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(u1_struct_0(B_105)))
      | ~ m1_subset_1(D_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | g1_orders_2(u1_struct_0(B_105),u1_orders_2(B_105)) != g1_orders_2(u1_struct_0(A_107),u1_orders_2(A_107))
      | ~ l1_orders_2(B_105)
      | ~ l1_orders_2(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_453,plain,(
    ! [A_107] :
      ( k4_waybel_0(A_107,'#skF_9') = k4_waybel_0('#skF_7','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0(A_107)))
      | g1_orders_2(u1_struct_0(A_107),u1_orders_2(A_107)) != g1_orders_2(u1_struct_0('#skF_7'),u1_orders_2('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ l1_orders_2(A_107) ) ),
    inference(resolution,[status(thm)],[c_64,c_443])).

tff(c_520,plain,(
    ! [A_112] :
      ( k4_waybel_0(A_112,'#skF_9') = k4_waybel_0('#skF_7','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0(A_112)))
      | g1_orders_2(u1_struct_0(A_112),u1_orders_2(A_112)) != g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8'))
      | ~ l1_orders_2(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_453])).

tff(c_522,plain,
    ( k4_waybel_0('#skF_7','#skF_9') = k4_waybel_0('#skF_8','#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_79,c_520])).

tff(c_527,plain,(
    k4_waybel_0('#skF_7','#skF_9') = k4_waybel_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_522])).

tff(c_78,plain,
    ( v12_waybel_0('#skF_9','#skF_7')
    | v13_waybel_0('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_118,plain,(
    v13_waybel_0('#skF_9','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_336,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k4_waybel_0(A_92,B_93),B_93)
      | ~ v13_waybel_0(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_orders_2(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_346,plain,
    ( r1_tarski(k4_waybel_0('#skF_7','#skF_9'),'#skF_9')
    | ~ v13_waybel_0('#skF_9','#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_336])).

tff(c_354,plain,(
    r1_tarski(k4_waybel_0('#skF_7','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_118,c_346])).

tff(c_533,plain,(
    r1_tarski(k4_waybel_0('#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_354])).

tff(c_54,plain,(
    ! [B_41,A_39] :
      ( v13_waybel_0(B_41,A_39)
      | ~ r1_tarski(k4_waybel_0(A_39,B_41),B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_543,plain,
    ( v13_waybel_0('#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_533,c_54])).

tff(c_546,plain,(
    v13_waybel_0('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_79,c_543])).

tff(c_548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_546])).

tff(c_549,plain,(
    ~ v12_waybel_0('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_824,plain,(
    ! [B_145,D_146,A_147] :
      ( k3_waybel_0(B_145,D_146) = k3_waybel_0(A_147,D_146)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(B_145)))
      | ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(A_147)))
      | g1_orders_2(u1_struct_0(B_145),u1_orders_2(B_145)) != g1_orders_2(u1_struct_0(A_147),u1_orders_2(A_147))
      | ~ l1_orders_2(B_145)
      | ~ l1_orders_2(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_834,plain,(
    ! [A_147] :
      ( k3_waybel_0(A_147,'#skF_9') = k3_waybel_0('#skF_7','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0(A_147)))
      | g1_orders_2(u1_struct_0(A_147),u1_orders_2(A_147)) != g1_orders_2(u1_struct_0('#skF_7'),u1_orders_2('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ l1_orders_2(A_147) ) ),
    inference(resolution,[status(thm)],[c_64,c_824])).

tff(c_979,plain,(
    ! [A_159] :
      ( k3_waybel_0(A_159,'#skF_9') = k3_waybel_0('#skF_7','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0(A_159)))
      | g1_orders_2(u1_struct_0(A_159),u1_orders_2(A_159)) != g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8'))
      | ~ l1_orders_2(A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_834])).

tff(c_981,plain,
    ( k3_waybel_0('#skF_7','#skF_9') = k3_waybel_0('#skF_8','#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_79,c_979])).

tff(c_986,plain,(
    k3_waybel_0('#skF_7','#skF_9') = k3_waybel_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_981])).

tff(c_550,plain,(
    v13_waybel_0('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_74,plain,
    ( v12_waybel_0('#skF_9','#skF_7')
    | ~ v13_waybel_0('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_81,plain,
    ( v12_waybel_0('#skF_9','#skF_7')
    | ~ v13_waybel_0('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_74])).

tff(c_557,plain,(
    v12_waybel_0('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_81])).

tff(c_788,plain,(
    ! [A_141,B_142] :
      ( r1_tarski(k3_waybel_0(A_141,B_142),B_142)
      | ~ v12_waybel_0(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_orders_2(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_798,plain,
    ( r1_tarski(k3_waybel_0('#skF_7','#skF_9'),'#skF_9')
    | ~ v12_waybel_0('#skF_9','#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_788])).

tff(c_806,plain,(
    r1_tarski(k3_waybel_0('#skF_7','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_557,c_798])).

tff(c_998,plain,(
    r1_tarski(k3_waybel_0('#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_806])).

tff(c_50,plain,(
    ! [B_38,A_36] :
      ( v12_waybel_0(B_38,A_36)
      | ~ r1_tarski(k3_waybel_0(A_36,B_38),B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1022,plain,
    ( v12_waybel_0('#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_998,c_50])).

tff(c_1025,plain,(
    v12_waybel_0('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_79,c_1022])).

tff(c_1027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_549,c_1025])).

tff(c_1029,plain,(
    ~ v13_waybel_0('#skF_9','#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_76,plain,
    ( ~ v12_waybel_0('#skF_10','#skF_8')
    | v13_waybel_0('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_80,plain,
    ( ~ v12_waybel_0('#skF_9','#skF_8')
    | v13_waybel_0('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_76])).

tff(c_1053,plain,(
    ~ v12_waybel_0('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1029,c_80])).

tff(c_1310,plain,(
    ! [B_199,D_200,A_201] :
      ( k3_waybel_0(B_199,D_200) = k3_waybel_0(A_201,D_200)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(u1_struct_0(B_199)))
      | ~ m1_subset_1(D_200,k1_zfmisc_1(u1_struct_0(A_201)))
      | g1_orders_2(u1_struct_0(B_199),u1_orders_2(B_199)) != g1_orders_2(u1_struct_0(A_201),u1_orders_2(A_201))
      | ~ l1_orders_2(B_199)
      | ~ l1_orders_2(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1320,plain,(
    ! [A_201] :
      ( k3_waybel_0(A_201,'#skF_9') = k3_waybel_0('#skF_7','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0(A_201)))
      | g1_orders_2(u1_struct_0(A_201),u1_orders_2(A_201)) != g1_orders_2(u1_struct_0('#skF_7'),u1_orders_2('#skF_7'))
      | ~ l1_orders_2('#skF_7')
      | ~ l1_orders_2(A_201) ) ),
    inference(resolution,[status(thm)],[c_64,c_1310])).

tff(c_1465,plain,(
    ! [A_213] :
      ( k3_waybel_0(A_213,'#skF_9') = k3_waybel_0('#skF_7','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0(A_213)))
      | g1_orders_2(u1_struct_0(A_213),u1_orders_2(A_213)) != g1_orders_2(u1_struct_0('#skF_8'),u1_orders_2('#skF_8'))
      | ~ l1_orders_2(A_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1320])).

tff(c_1467,plain,
    ( k3_waybel_0('#skF_7','#skF_9') = k3_waybel_0('#skF_8','#skF_9')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_79,c_1465])).

tff(c_1472,plain,(
    k3_waybel_0('#skF_7','#skF_9') = k3_waybel_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1467])).

tff(c_1028,plain,(
    v12_waybel_0('#skF_9','#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1273,plain,(
    ! [A_193,B_194] :
      ( r1_tarski(k3_waybel_0(A_193,B_194),B_194)
      | ~ v12_waybel_0(B_194,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_orders_2(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1283,plain,
    ( r1_tarski(k3_waybel_0('#skF_7','#skF_9'),'#skF_9')
    | ~ v12_waybel_0('#skF_9','#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_1273])).

tff(c_1291,plain,(
    r1_tarski(k3_waybel_0('#skF_7','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1028,c_1283])).

tff(c_1478,plain,(
    r1_tarski(k3_waybel_0('#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1472,c_1291])).

tff(c_1488,plain,
    ( v12_waybel_0('#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_1478,c_50])).

tff(c_1491,plain,(
    v12_waybel_0('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_79,c_1488])).

tff(c_1493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1053,c_1491])).

%------------------------------------------------------------------------------
