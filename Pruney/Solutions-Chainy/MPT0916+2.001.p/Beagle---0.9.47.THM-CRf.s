%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:09 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 475 expanded)
%              Number of leaves         :   30 ( 161 expanded)
%              Depth                    :    9
%              Number of atoms          :  270 (1336 expanded)
%              Number of equality atoms :   97 ( 435 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_67,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_28,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_614,plain,(
    ! [B_158,A_159] :
      ( v1_xboole_0(B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_159))
      | ~ v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_624,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_614])).

tff(c_629,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_624])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_628,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_614])).

tff(c_630,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_628])).

tff(c_24,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_641,plain,(
    ! [A_166,B_167,C_168] : k2_zfmisc_1(k2_zfmisc_1(A_166,B_167),C_168) = k3_zfmisc_1(A_166,B_167,C_168) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_11,C_13,B_12] :
      ( r2_hidden(k2_mcart_1(A_11),C_13)
      | ~ r2_hidden(A_11,k2_zfmisc_1(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_660,plain,(
    ! [A_169,C_170,A_171,B_172] :
      ( r2_hidden(k2_mcart_1(A_169),C_170)
      | ~ r2_hidden(A_169,k3_zfmisc_1(A_171,B_172,C_170)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_12])).

tff(c_666,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_660])).

tff(c_44,plain,(
    ! [B_33,A_34] :
      ( v1_xboole_0(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_44])).

tff(c_57,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_22,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_43,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_56,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_55,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_44])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_26,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_122,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k7_mcart_1(A_50,B_51,C_52,D_53) = k2_mcart_1(D_53)
      | ~ m1_subset_1(D_53,k3_zfmisc_1(A_50,B_51,C_52))
      | k1_xboole_0 = C_52
      | k1_xboole_0 = B_51
      | k1_xboole_0 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_126,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_122])).

tff(c_159,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_161,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_6])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_161])).

tff(c_165,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_183,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k5_mcart_1(A_66,B_67,C_68,D_69) = k1_mcart_1(k1_mcart_1(D_69))
      | ~ m1_subset_1(D_69,k3_zfmisc_1(A_66,B_67,C_68))
      | k1_xboole_0 = C_68
      | k1_xboole_0 = B_67
      | k1_xboole_0 = A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_186,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_183])).

tff(c_189,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_186])).

tff(c_191,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_195,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_6])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_195])).

tff(c_198,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_204,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_70,plain,(
    ! [A_41,B_42,C_43] : k2_zfmisc_1(k2_zfmisc_1(A_41,B_42),C_43) = k3_zfmisc_1(A_41,B_42,C_43) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden(k1_mcart_1(A_11),B_12)
      | ~ r2_hidden(A_11,k2_zfmisc_1(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_263,plain,(
    ! [A_78,A_79,B_80,C_81] :
      ( r2_hidden(k1_mcart_1(A_78),k2_zfmisc_1(A_79,B_80))
      | ~ r2_hidden(A_78,k3_zfmisc_1(A_79,B_80,C_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_14])).

tff(c_280,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_24,c_263])).

tff(c_283,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_280,c_14])).

tff(c_290,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_283])).

tff(c_292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_290])).

tff(c_293,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_299,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_6])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_299])).

tff(c_302,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_35,C_36,B_37] :
      ( r2_hidden(k2_mcart_1(A_35),C_36)
      | ~ r2_hidden(A_35,k2_zfmisc_1(B_37,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_345,plain,(
    ! [B_96,C_97] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_96,C_97))),C_97)
      | v1_xboole_0(k2_zfmisc_1(B_96,C_97)) ) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_364,plain,(
    ! [C_97,B_96] :
      ( ~ v1_xboole_0(C_97)
      | v1_xboole_0(k2_zfmisc_1(B_96,C_97)) ) ),
    inference(resolution,[status(thm)],[c_345,c_2])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_304,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden(k1_mcart_1(A_82),B_83)
      | ~ r2_hidden(A_82,k2_zfmisc_1(B_83,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_380,plain,(
    ! [B_107,C_108] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_107,C_108))),B_107)
      | v1_xboole_0(k2_zfmisc_1(B_107,C_108)) ) ),
    inference(resolution,[status(thm)],[c_4,c_304])).

tff(c_403,plain,(
    ! [B_109,C_110] :
      ( ~ v1_xboole_0(B_109)
      | v1_xboole_0(k2_zfmisc_1(B_109,C_110)) ) ),
    inference(resolution,[status(thm)],[c_380,c_2])).

tff(c_415,plain,(
    ! [A_111,B_112,C_113] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_111,B_112))
      | v1_xboole_0(k3_zfmisc_1(A_111,B_112,C_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_403])).

tff(c_42,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_2])).

tff(c_419,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_415,c_42])).

tff(c_425,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_364,c_419])).

tff(c_430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_425])).

tff(c_431,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_439,plain,(
    ! [A_117,B_118,C_119] :
      ( r2_hidden(k1_mcart_1(A_117),B_118)
      | ~ r2_hidden(A_117,k2_zfmisc_1(B_118,C_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_510,plain,(
    ! [B_138,C_139] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_138,C_139))),B_138)
      | v1_xboole_0(k2_zfmisc_1(B_138,C_139)) ) ),
    inference(resolution,[status(thm)],[c_4,c_439])).

tff(c_531,plain,(
    ! [B_138,C_139] :
      ( ~ v1_xboole_0(B_138)
      | v1_xboole_0(k2_zfmisc_1(B_138,C_139)) ) ),
    inference(resolution,[status(thm)],[c_510,c_2])).

tff(c_541,plain,(
    ! [B_140,C_141] :
      ( ~ v1_xboole_0(B_140)
      | v1_xboole_0(k2_zfmisc_1(B_140,C_141)) ) ),
    inference(resolution,[status(thm)],[c_510,c_2])).

tff(c_545,plain,(
    ! [A_142,B_143,C_144] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_142,B_143))
      | v1_xboole_0(k3_zfmisc_1(A_142,B_143,C_144)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_541])).

tff(c_549,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_545,c_42])).

tff(c_552,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_531,c_549])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_552])).

tff(c_560,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_569,plain,(
    ! [A_148,B_149,C_150] : k2_zfmisc_1(k2_zfmisc_1(A_148,B_149),C_150) = k3_zfmisc_1(A_148,B_149,C_150) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_593,plain,(
    ! [A_154,C_155,A_156,B_157] :
      ( r2_hidden(k2_mcart_1(A_154),C_155)
      | ~ r2_hidden(A_154,k3_zfmisc_1(A_156,B_157,C_155)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_12])).

tff(c_599,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_593])).

tff(c_603,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_599,c_2])).

tff(c_607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_603])).

tff(c_609,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_613,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_609,c_2])).

tff(c_620,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_614])).

tff(c_627,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_613,c_620])).

tff(c_709,plain,(
    ! [A_180,B_181,C_182,D_183] :
      ( k7_mcart_1(A_180,B_181,C_182,D_183) = k2_mcart_1(D_183)
      | ~ m1_subset_1(D_183,k3_zfmisc_1(A_180,B_181,C_182))
      | k1_xboole_0 = C_182
      | k1_xboole_0 = B_181
      | k1_xboole_0 = A_180 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_713,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_709])).

tff(c_743,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_713])).

tff(c_745,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_6])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_627,c_745])).

tff(c_748,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_713])).

tff(c_755,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_748])).

tff(c_608,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_672,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_608])).

tff(c_756,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_672])).

tff(c_759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_756])).

tff(c_760,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_769,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_760])).

tff(c_773,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_6])).

tff(c_775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_630,c_773])).

tff(c_777,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_760])).

tff(c_749,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_713])).

tff(c_762,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( k6_mcart_1(A_191,B_192,C_193,D_194) = k2_mcart_1(k1_mcart_1(D_194))
      | ~ m1_subset_1(D_194,k3_zfmisc_1(A_191,B_192,C_193))
      | k1_xboole_0 = C_193
      | k1_xboole_0 = B_192
      | k1_xboole_0 = A_191 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_765,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_762])).

tff(c_768,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_749,c_765])).

tff(c_778,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_777,c_768])).

tff(c_779,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_778])).

tff(c_784,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_6])).

tff(c_786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_629,c_784])).

tff(c_788,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_778])).

tff(c_776,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_760])).

tff(c_789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_788,c_776])).

tff(c_790,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_608])).

tff(c_796,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k7_mcart_1(A_195,B_196,C_197,D_198) = k2_mcart_1(D_198)
      | ~ m1_subset_1(D_198,k3_zfmisc_1(A_195,B_196,C_197))
      | k1_xboole_0 = C_197
      | k1_xboole_0 = B_196
      | k1_xboole_0 = A_195 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_800,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_796])).

tff(c_831,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_800])).

tff(c_833,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_6])).

tff(c_835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_627,c_833])).

tff(c_837,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_800])).

tff(c_870,plain,(
    ! [A_213,B_214,C_215,D_216] :
      ( k6_mcart_1(A_213,B_214,C_215,D_216) = k2_mcart_1(k1_mcart_1(D_216))
      | ~ m1_subset_1(D_216,k3_zfmisc_1(A_213,B_214,C_215))
      | k1_xboole_0 = C_215
      | k1_xboole_0 = B_214
      | k1_xboole_0 = A_213 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_873,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_870])).

tff(c_876,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_837,c_873])).

tff(c_886,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_876])).

tff(c_890,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_6])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_630,c_890])).

tff(c_893,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_901,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_893])).

tff(c_960,plain,(
    ! [A_225,A_226,B_227,C_228] :
      ( r2_hidden(k1_mcart_1(A_225),k2_zfmisc_1(A_226,B_227))
      | ~ r2_hidden(A_225,k3_zfmisc_1(A_226,B_227,C_228)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_14])).

tff(c_977,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_24,c_960])).

tff(c_980,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_977,c_12])).

tff(c_987,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_980])).

tff(c_989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_790,c_987])).

tff(c_990,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_893])).

tff(c_996,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_990,c_6])).

tff(c_998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_629,c_996])).

tff(c_999,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_628])).

tff(c_1024,plain,(
    ! [A_235,C_236,B_237] :
      ( r2_hidden(k2_mcart_1(A_235),C_236)
      | ~ r2_hidden(A_235,k2_zfmisc_1(B_237,C_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1116,plain,(
    ! [B_257,C_258] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_257,C_258))),C_258)
      | v1_xboole_0(k2_zfmisc_1(B_257,C_258)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1024])).

tff(c_1137,plain,(
    ! [C_259,B_260] :
      ( ~ v1_xboole_0(C_259)
      | v1_xboole_0(k2_zfmisc_1(B_260,C_259)) ) ),
    inference(resolution,[status(thm)],[c_1116,c_2])).

tff(c_1001,plain,(
    ! [A_229,B_230,C_231] :
      ( r2_hidden(k1_mcart_1(A_229),B_230)
      | ~ r2_hidden(A_229,k2_zfmisc_1(B_230,C_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1048,plain,(
    ! [B_246,C_247] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_246,C_247))),B_246)
      | v1_xboole_0(k2_zfmisc_1(B_246,C_247)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1001])).

tff(c_1071,plain,(
    ! [B_248,C_249] :
      ( ~ v1_xboole_0(B_248)
      | v1_xboole_0(k2_zfmisc_1(B_248,C_249)) ) ),
    inference(resolution,[status(thm)],[c_1048,c_2])).

tff(c_1075,plain,(
    ! [A_250,B_251,C_252] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_250,B_251))
      | v1_xboole_0(k3_zfmisc_1(A_250,B_251,C_252)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1071])).

tff(c_1079,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1075,c_42])).

tff(c_1140,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1137,c_1079])).

tff(c_1147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_1140])).

tff(c_1148,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_1174,plain,(
    ! [A_267,C_268,B_269] :
      ( r2_hidden(k2_mcart_1(A_267),C_268)
      | ~ r2_hidden(A_267,k2_zfmisc_1(B_269,C_268)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1181,plain,(
    ! [A_270,C_271,A_272,B_273] :
      ( r2_hidden(k2_mcart_1(A_270),C_271)
      | ~ r2_hidden(A_270,k3_zfmisc_1(A_272,B_273,C_271)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1174])).

tff(c_1187,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_1181])).

tff(c_1191,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1187,c_2])).

tff(c_1195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_1191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:53:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.51  
% 3.19/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.52  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 3.19/1.52  
% 3.19/1.52  %Foreground sorts:
% 3.19/1.52  
% 3.19/1.52  
% 3.19/1.52  %Background operators:
% 3.19/1.52  
% 3.19/1.52  
% 3.19/1.52  %Foreground operators:
% 3.19/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.19/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.19/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.52  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.19/1.52  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.19/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.19/1.52  tff('#skF_8', type, '#skF_8': $i).
% 3.19/1.52  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.19/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.52  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.19/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.52  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.19/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.52  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.19/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.19/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.19/1.52  
% 3.38/1.54  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 3.38/1.54  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.38/1.54  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.38/1.54  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.38/1.54  tff(f_67, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.38/1.54  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.38/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.38/1.54  tff(c_28, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.38/1.54  tff(c_614, plain, (![B_158, A_159]: (v1_xboole_0(B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(A_159)) | ~v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.38/1.54  tff(c_624, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_614])).
% 3.38/1.54  tff(c_629, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_624])).
% 3.38/1.54  tff(c_30, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.38/1.54  tff(c_628, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_614])).
% 3.38/1.54  tff(c_630, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_628])).
% 3.38/1.54  tff(c_24, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.38/1.54  tff(c_641, plain, (![A_166, B_167, C_168]: (k2_zfmisc_1(k2_zfmisc_1(A_166, B_167), C_168)=k3_zfmisc_1(A_166, B_167, C_168))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.54  tff(c_12, plain, (![A_11, C_13, B_12]: (r2_hidden(k2_mcart_1(A_11), C_13) | ~r2_hidden(A_11, k2_zfmisc_1(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.38/1.54  tff(c_660, plain, (![A_169, C_170, A_171, B_172]: (r2_hidden(k2_mcart_1(A_169), C_170) | ~r2_hidden(A_169, k3_zfmisc_1(A_171, B_172, C_170)))), inference(superposition, [status(thm), theory('equality')], [c_641, c_12])).
% 3.38/1.54  tff(c_666, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_24, c_660])).
% 3.38/1.54  tff(c_44, plain, (![B_33, A_34]: (v1_xboole_0(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.38/1.54  tff(c_54, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_44])).
% 3.38/1.54  tff(c_57, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 3.38/1.54  tff(c_22, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.38/1.54  tff(c_43, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_22])).
% 3.38/1.54  tff(c_56, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_44])).
% 3.38/1.54  tff(c_64, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 3.38/1.54  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.38/1.54  tff(c_55, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_44])).
% 3.38/1.54  tff(c_58, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_55])).
% 3.38/1.54  tff(c_26, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.38/1.54  tff(c_122, plain, (![A_50, B_51, C_52, D_53]: (k7_mcart_1(A_50, B_51, C_52, D_53)=k2_mcart_1(D_53) | ~m1_subset_1(D_53, k3_zfmisc_1(A_50, B_51, C_52)) | k1_xboole_0=C_52 | k1_xboole_0=B_51 | k1_xboole_0=A_50)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.38/1.54  tff(c_126, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_26, c_122])).
% 3.38/1.54  tff(c_159, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_126])).
% 3.38/1.54  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.38/1.54  tff(c_161, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_6])).
% 3.38/1.54  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_161])).
% 3.38/1.54  tff(c_165, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_126])).
% 3.38/1.54  tff(c_183, plain, (![A_66, B_67, C_68, D_69]: (k5_mcart_1(A_66, B_67, C_68, D_69)=k1_mcart_1(k1_mcart_1(D_69)) | ~m1_subset_1(D_69, k3_zfmisc_1(A_66, B_67, C_68)) | k1_xboole_0=C_68 | k1_xboole_0=B_67 | k1_xboole_0=A_66)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.38/1.54  tff(c_186, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_26, c_183])).
% 3.38/1.54  tff(c_189, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_165, c_186])).
% 3.38/1.54  tff(c_191, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_189])).
% 3.38/1.54  tff(c_195, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_6])).
% 3.38/1.54  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_195])).
% 3.38/1.54  tff(c_198, plain, (k1_xboole_0='#skF_4' | k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_189])).
% 3.38/1.54  tff(c_204, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_198])).
% 3.38/1.54  tff(c_70, plain, (![A_41, B_42, C_43]: (k2_zfmisc_1(k2_zfmisc_1(A_41, B_42), C_43)=k3_zfmisc_1(A_41, B_42, C_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.54  tff(c_14, plain, (![A_11, B_12, C_13]: (r2_hidden(k1_mcart_1(A_11), B_12) | ~r2_hidden(A_11, k2_zfmisc_1(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.38/1.54  tff(c_263, plain, (![A_78, A_79, B_80, C_81]: (r2_hidden(k1_mcart_1(A_78), k2_zfmisc_1(A_79, B_80)) | ~r2_hidden(A_78, k3_zfmisc_1(A_79, B_80, C_81)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_14])).
% 3.38/1.54  tff(c_280, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_263])).
% 3.38/1.54  tff(c_283, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_280, c_14])).
% 3.38/1.54  tff(c_290, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_283])).
% 3.38/1.54  tff(c_292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_290])).
% 3.38/1.54  tff(c_293, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_198])).
% 3.38/1.54  tff(c_299, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_6])).
% 3.38/1.54  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_299])).
% 3.38/1.54  tff(c_302, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 3.38/1.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.54  tff(c_59, plain, (![A_35, C_36, B_37]: (r2_hidden(k2_mcart_1(A_35), C_36) | ~r2_hidden(A_35, k2_zfmisc_1(B_37, C_36)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.38/1.54  tff(c_345, plain, (![B_96, C_97]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_96, C_97))), C_97) | v1_xboole_0(k2_zfmisc_1(B_96, C_97)))), inference(resolution, [status(thm)], [c_4, c_59])).
% 3.38/1.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.54  tff(c_364, plain, (![C_97, B_96]: (~v1_xboole_0(C_97) | v1_xboole_0(k2_zfmisc_1(B_96, C_97)))), inference(resolution, [status(thm)], [c_345, c_2])).
% 3.38/1.54  tff(c_10, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.54  tff(c_304, plain, (![A_82, B_83, C_84]: (r2_hidden(k1_mcart_1(A_82), B_83) | ~r2_hidden(A_82, k2_zfmisc_1(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.38/1.54  tff(c_380, plain, (![B_107, C_108]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_107, C_108))), B_107) | v1_xboole_0(k2_zfmisc_1(B_107, C_108)))), inference(resolution, [status(thm)], [c_4, c_304])).
% 3.38/1.54  tff(c_403, plain, (![B_109, C_110]: (~v1_xboole_0(B_109) | v1_xboole_0(k2_zfmisc_1(B_109, C_110)))), inference(resolution, [status(thm)], [c_380, c_2])).
% 3.38/1.54  tff(c_415, plain, (![A_111, B_112, C_113]: (~v1_xboole_0(k2_zfmisc_1(A_111, B_112)) | v1_xboole_0(k3_zfmisc_1(A_111, B_112, C_113)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_403])).
% 3.38/1.54  tff(c_42, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_2])).
% 3.38/1.54  tff(c_419, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_415, c_42])).
% 3.38/1.54  tff(c_425, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_364, c_419])).
% 3.38/1.54  tff(c_430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_302, c_425])).
% 3.38/1.54  tff(c_431, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_55])).
% 3.38/1.54  tff(c_439, plain, (![A_117, B_118, C_119]: (r2_hidden(k1_mcart_1(A_117), B_118) | ~r2_hidden(A_117, k2_zfmisc_1(B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.38/1.54  tff(c_510, plain, (![B_138, C_139]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_138, C_139))), B_138) | v1_xboole_0(k2_zfmisc_1(B_138, C_139)))), inference(resolution, [status(thm)], [c_4, c_439])).
% 3.38/1.54  tff(c_531, plain, (![B_138, C_139]: (~v1_xboole_0(B_138) | v1_xboole_0(k2_zfmisc_1(B_138, C_139)))), inference(resolution, [status(thm)], [c_510, c_2])).
% 3.38/1.54  tff(c_541, plain, (![B_140, C_141]: (~v1_xboole_0(B_140) | v1_xboole_0(k2_zfmisc_1(B_140, C_141)))), inference(resolution, [status(thm)], [c_510, c_2])).
% 3.38/1.54  tff(c_545, plain, (![A_142, B_143, C_144]: (~v1_xboole_0(k2_zfmisc_1(A_142, B_143)) | v1_xboole_0(k3_zfmisc_1(A_142, B_143, C_144)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_541])).
% 3.38/1.54  tff(c_549, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_545, c_42])).
% 3.38/1.54  tff(c_552, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_531, c_549])).
% 3.38/1.54  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_431, c_552])).
% 3.38/1.54  tff(c_560, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 3.38/1.54  tff(c_569, plain, (![A_148, B_149, C_150]: (k2_zfmisc_1(k2_zfmisc_1(A_148, B_149), C_150)=k3_zfmisc_1(A_148, B_149, C_150))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.54  tff(c_593, plain, (![A_154, C_155, A_156, B_157]: (r2_hidden(k2_mcart_1(A_154), C_155) | ~r2_hidden(A_154, k3_zfmisc_1(A_156, B_157, C_155)))), inference(superposition, [status(thm), theory('equality')], [c_569, c_12])).
% 3.38/1.54  tff(c_599, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_24, c_593])).
% 3.38/1.54  tff(c_603, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_599, c_2])).
% 3.38/1.54  tff(c_607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_560, c_603])).
% 3.38/1.54  tff(c_609, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_22])).
% 3.38/1.54  tff(c_613, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_609, c_2])).
% 3.38/1.54  tff(c_620, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_614])).
% 3.38/1.54  tff(c_627, plain, (~v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_613, c_620])).
% 3.38/1.54  tff(c_709, plain, (![A_180, B_181, C_182, D_183]: (k7_mcart_1(A_180, B_181, C_182, D_183)=k2_mcart_1(D_183) | ~m1_subset_1(D_183, k3_zfmisc_1(A_180, B_181, C_182)) | k1_xboole_0=C_182 | k1_xboole_0=B_181 | k1_xboole_0=A_180)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.38/1.54  tff(c_713, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_26, c_709])).
% 3.38/1.54  tff(c_743, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_713])).
% 3.38/1.54  tff(c_745, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_743, c_6])).
% 3.38/1.54  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_627, c_745])).
% 3.38/1.54  tff(c_748, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_713])).
% 3.38/1.54  tff(c_755, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_748])).
% 3.38/1.54  tff(c_608, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_22])).
% 3.38/1.54  tff(c_672, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_608])).
% 3.38/1.54  tff(c_756, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_755, c_672])).
% 3.38/1.54  tff(c_759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_666, c_756])).
% 3.38/1.54  tff(c_760, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_748])).
% 3.38/1.54  tff(c_769, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_760])).
% 3.38/1.54  tff(c_773, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_769, c_6])).
% 3.38/1.54  tff(c_775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_630, c_773])).
% 3.38/1.54  tff(c_777, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_760])).
% 3.38/1.54  tff(c_749, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_713])).
% 3.38/1.54  tff(c_762, plain, (![A_191, B_192, C_193, D_194]: (k6_mcart_1(A_191, B_192, C_193, D_194)=k2_mcart_1(k1_mcart_1(D_194)) | ~m1_subset_1(D_194, k3_zfmisc_1(A_191, B_192, C_193)) | k1_xboole_0=C_193 | k1_xboole_0=B_192 | k1_xboole_0=A_191)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.38/1.54  tff(c_765, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_26, c_762])).
% 3.38/1.54  tff(c_768, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_749, c_765])).
% 3.38/1.54  tff(c_778, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_777, c_768])).
% 3.38/1.54  tff(c_779, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_778])).
% 3.38/1.54  tff(c_784, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_779, c_6])).
% 3.38/1.54  tff(c_786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_629, c_784])).
% 3.38/1.54  tff(c_788, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_778])).
% 3.38/1.54  tff(c_776, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_760])).
% 3.38/1.54  tff(c_789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_788, c_776])).
% 3.38/1.54  tff(c_790, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_608])).
% 3.38/1.54  tff(c_796, plain, (![A_195, B_196, C_197, D_198]: (k7_mcart_1(A_195, B_196, C_197, D_198)=k2_mcart_1(D_198) | ~m1_subset_1(D_198, k3_zfmisc_1(A_195, B_196, C_197)) | k1_xboole_0=C_197 | k1_xboole_0=B_196 | k1_xboole_0=A_195)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.38/1.54  tff(c_800, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_26, c_796])).
% 3.38/1.54  tff(c_831, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_800])).
% 3.38/1.54  tff(c_833, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_831, c_6])).
% 3.38/1.54  tff(c_835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_627, c_833])).
% 3.38/1.54  tff(c_837, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_800])).
% 3.38/1.54  tff(c_870, plain, (![A_213, B_214, C_215, D_216]: (k6_mcart_1(A_213, B_214, C_215, D_216)=k2_mcart_1(k1_mcart_1(D_216)) | ~m1_subset_1(D_216, k3_zfmisc_1(A_213, B_214, C_215)) | k1_xboole_0=C_215 | k1_xboole_0=B_214 | k1_xboole_0=A_213)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.38/1.54  tff(c_873, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_26, c_870])).
% 3.38/1.54  tff(c_876, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_837, c_873])).
% 3.38/1.54  tff(c_886, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_876])).
% 3.38/1.54  tff(c_890, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_886, c_6])).
% 3.38/1.54  tff(c_892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_630, c_890])).
% 3.38/1.54  tff(c_893, plain, (k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_876])).
% 3.38/1.54  tff(c_901, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_893])).
% 3.38/1.54  tff(c_960, plain, (![A_225, A_226, B_227, C_228]: (r2_hidden(k1_mcart_1(A_225), k2_zfmisc_1(A_226, B_227)) | ~r2_hidden(A_225, k3_zfmisc_1(A_226, B_227, C_228)))), inference(superposition, [status(thm), theory('equality')], [c_641, c_14])).
% 3.38/1.54  tff(c_977, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_960])).
% 3.38/1.54  tff(c_980, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_977, c_12])).
% 3.38/1.54  tff(c_987, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_901, c_980])).
% 3.38/1.54  tff(c_989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_790, c_987])).
% 3.38/1.54  tff(c_990, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_893])).
% 3.38/1.54  tff(c_996, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_990, c_6])).
% 3.38/1.54  tff(c_998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_629, c_996])).
% 3.38/1.54  tff(c_999, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_628])).
% 3.38/1.54  tff(c_1024, plain, (![A_235, C_236, B_237]: (r2_hidden(k2_mcart_1(A_235), C_236) | ~r2_hidden(A_235, k2_zfmisc_1(B_237, C_236)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.38/1.54  tff(c_1116, plain, (![B_257, C_258]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_257, C_258))), C_258) | v1_xboole_0(k2_zfmisc_1(B_257, C_258)))), inference(resolution, [status(thm)], [c_4, c_1024])).
% 3.38/1.54  tff(c_1137, plain, (![C_259, B_260]: (~v1_xboole_0(C_259) | v1_xboole_0(k2_zfmisc_1(B_260, C_259)))), inference(resolution, [status(thm)], [c_1116, c_2])).
% 3.38/1.54  tff(c_1001, plain, (![A_229, B_230, C_231]: (r2_hidden(k1_mcart_1(A_229), B_230) | ~r2_hidden(A_229, k2_zfmisc_1(B_230, C_231)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.38/1.54  tff(c_1048, plain, (![B_246, C_247]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_246, C_247))), B_246) | v1_xboole_0(k2_zfmisc_1(B_246, C_247)))), inference(resolution, [status(thm)], [c_4, c_1001])).
% 3.38/1.54  tff(c_1071, plain, (![B_248, C_249]: (~v1_xboole_0(B_248) | v1_xboole_0(k2_zfmisc_1(B_248, C_249)))), inference(resolution, [status(thm)], [c_1048, c_2])).
% 3.38/1.54  tff(c_1075, plain, (![A_250, B_251, C_252]: (~v1_xboole_0(k2_zfmisc_1(A_250, B_251)) | v1_xboole_0(k3_zfmisc_1(A_250, B_251, C_252)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1071])).
% 3.38/1.54  tff(c_1079, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1075, c_42])).
% 3.38/1.54  tff(c_1140, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1137, c_1079])).
% 3.38/1.54  tff(c_1147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_999, c_1140])).
% 3.38/1.54  tff(c_1148, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_624])).
% 3.38/1.54  tff(c_1174, plain, (![A_267, C_268, B_269]: (r2_hidden(k2_mcart_1(A_267), C_268) | ~r2_hidden(A_267, k2_zfmisc_1(B_269, C_268)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.38/1.54  tff(c_1181, plain, (![A_270, C_271, A_272, B_273]: (r2_hidden(k2_mcart_1(A_270), C_271) | ~r2_hidden(A_270, k3_zfmisc_1(A_272, B_273, C_271)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1174])).
% 3.38/1.54  tff(c_1187, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_24, c_1181])).
% 3.38/1.54  tff(c_1191, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_1187, c_2])).
% 3.38/1.54  tff(c_1195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1148, c_1191])).
% 3.38/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.54  
% 3.38/1.54  Inference rules
% 3.38/1.54  ----------------------
% 3.38/1.54  #Ref     : 0
% 3.38/1.54  #Sup     : 244
% 3.38/1.54  #Fact    : 0
% 3.38/1.54  #Define  : 0
% 3.38/1.54  #Split   : 32
% 3.38/1.54  #Chain   : 0
% 3.38/1.54  #Close   : 0
% 3.38/1.54  
% 3.38/1.54  Ordering : KBO
% 3.38/1.54  
% 3.38/1.54  Simplification rules
% 3.38/1.54  ----------------------
% 3.38/1.54  #Subsume      : 17
% 3.38/1.54  #Demod        : 173
% 3.38/1.54  #Tautology    : 43
% 3.38/1.54  #SimpNegUnit  : 24
% 3.38/1.54  #BackRed      : 59
% 3.38/1.54  
% 3.38/1.54  #Partial instantiations: 0
% 3.38/1.54  #Strategies tried      : 1
% 3.38/1.54  
% 3.38/1.54  Timing (in seconds)
% 3.38/1.54  ----------------------
% 3.38/1.54  Preprocessing        : 0.30
% 3.38/1.54  Parsing              : 0.16
% 3.38/1.54  CNF conversion       : 0.02
% 3.38/1.54  Main loop            : 0.46
% 3.38/1.54  Inferencing          : 0.17
% 3.38/1.54  Reduction            : 0.14
% 3.38/1.54  Demodulation         : 0.10
% 3.38/1.54  BG Simplification    : 0.02
% 3.38/1.54  Subsumption          : 0.07
% 3.38/1.54  Abstraction          : 0.03
% 3.38/1.54  MUC search           : 0.00
% 3.38/1.54  Cooper               : 0.00
% 3.38/1.54  Total                : 0.81
% 3.38/1.54  Index Insertion      : 0.00
% 3.38/1.54  Index Deletion       : 0.00
% 3.38/1.54  Index Matching       : 0.00
% 3.38/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
