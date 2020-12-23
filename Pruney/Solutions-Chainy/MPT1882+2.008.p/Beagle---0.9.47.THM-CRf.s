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
% DateTime   : Thu Dec  3 10:30:13 EST 2020

% Result     : Theorem 4.40s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 342 expanded)
%              Number of leaves         :   30 ( 126 expanded)
%              Depth                    :   13
%              Number of atoms          :  216 (1283 expanded)
%              Number of equality atoms :   19 (  86 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_87,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_91,plain,(
    ! [B_38] : k4_xboole_0(B_38,B_38) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_14,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    ! [B_38] : r1_tarski(k1_xboole_0,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_14])).

tff(c_52,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_63,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_18,plain,(
    ! [A_9] :
      ( v1_zfmisc_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_344,plain,(
    ! [A_64,B_65] :
      ( '#skF_1'(A_64,B_65) != B_65
      | v3_tex_2(B_65,A_64)
      | ~ v2_tex_2(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_347,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_344])).

tff(c_350,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_347])).

tff(c_351,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_350])).

tff(c_352,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_58,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_64,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_58])).

tff(c_1035,plain,(
    ! [B_93,A_94] :
      ( v2_tex_2(B_93,A_94)
      | ~ v1_zfmisc_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | v1_xboole_0(B_93)
      | ~ l1_pre_topc(A_94)
      | ~ v2_tdlat_3(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1038,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_1035])).

tff(c_1041,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_64,c_1038])).

tff(c_1043,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_352,c_1041])).

tff(c_1044,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_1045,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_1362,plain,(
    ! [B_106,A_107] :
      ( r1_tarski(B_106,'#skF_1'(A_107,B_106))
      | v3_tex_2(B_106,A_107)
      | ~ v2_tex_2(B_106,A_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1364,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_1362])).

tff(c_1367,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1045,c_1364])).

tff(c_1368,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_1367])).

tff(c_34,plain,(
    ! [B_23,A_21] :
      ( B_23 = A_21
      | ~ r1_tarski(A_21,B_23)
      | ~ v1_zfmisc_1(B_23)
      | v1_xboole_0(B_23)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1379,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1368,c_34])).

tff(c_1390,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1044,c_1379])).

tff(c_1399,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1390])).

tff(c_1403,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_1399])).

tff(c_1240,plain,(
    ! [A_100,B_101] :
      ( v2_tex_2('#skF_1'(A_100,B_101),A_100)
      | v3_tex_2(B_101,A_100)
      | ~ v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1242,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_1240])).

tff(c_1245,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1045,c_1242])).

tff(c_1246,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_1245])).

tff(c_1892,plain,(
    ! [A_132,B_133] :
      ( m1_subset_1('#skF_1'(A_132,B_133),k1_zfmisc_1(u1_struct_0(A_132)))
      | v3_tex_2(B_133,A_132)
      | ~ v2_tex_2(B_133,A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    ! [B_26,A_24] :
      ( v1_zfmisc_1(B_26)
      | ~ v2_tex_2(B_26,A_24)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | v1_xboole_0(B_26)
      | ~ l1_pre_topc(A_24)
      | ~ v2_tdlat_3(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2135,plain,(
    ! [A_168,B_169] :
      ( v1_zfmisc_1('#skF_1'(A_168,B_169))
      | ~ v2_tex_2('#skF_1'(A_168,B_169),A_168)
      | v1_xboole_0('#skF_1'(A_168,B_169))
      | ~ v2_tdlat_3(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168)
      | v3_tex_2(B_169,A_168)
      | ~ v2_tex_2(B_169,A_168)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(resolution,[status(thm)],[c_1892,c_38])).

tff(c_2139,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1246,c_2135])).

tff(c_2143,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_1045,c_48,c_46,c_2139])).

tff(c_2145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_50,c_1403,c_1399,c_2143])).

tff(c_2146,plain,(
    v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1390])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_72,plain,(
    ! [B_33,A_34] :
      ( ~ v1_xboole_0(B_33)
      | B_33 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_2156,plain,(
    '#skF_1'('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2146,c_75])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1381,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1368,c_4])).

tff(c_1393,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1044,c_1381])).

tff(c_2164,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2156,c_1393])).

tff(c_2171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2164])).

tff(c_2172,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2173,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2435,plain,(
    ! [B_197,A_198] :
      ( v2_tex_2(B_197,A_198)
      | ~ v3_tex_2(B_197,A_198)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2438,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_2435])).

tff(c_2441,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2173,c_2438])).

tff(c_2511,plain,(
    ! [B_216,A_217] :
      ( v1_zfmisc_1(B_216)
      | ~ v2_tex_2(B_216,A_217)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_217)))
      | v1_xboole_0(B_216)
      | ~ l1_pre_topc(A_217)
      | ~ v2_tdlat_3(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2517,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_2511])).

tff(c_2521,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_2441,c_2517])).

tff(c_2523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_2172,c_2521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.40/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/2.00  
% 4.40/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/2.00  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.40/2.00  
% 4.40/2.00  %Foreground sorts:
% 4.40/2.00  
% 4.40/2.00  
% 4.40/2.00  %Background operators:
% 4.40/2.00  
% 4.40/2.00  
% 4.40/2.00  %Foreground operators:
% 4.40/2.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.40/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.40/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.40/2.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.40/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.40/2.00  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.40/2.00  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.40/2.00  tff('#skF_2', type, '#skF_2': $i).
% 4.40/2.00  tff('#skF_3', type, '#skF_3': $i).
% 4.40/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.40/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/2.00  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.40/2.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.40/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.40/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.40/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.40/2.00  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.40/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.40/2.00  
% 4.40/2.01  tff(f_126, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 4.40/2.01  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.40/2.01  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.40/2.01  tff(f_38, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.40/2.01  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 4.40/2.01  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 4.40/2.01  tff(f_106, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 4.40/2.01  tff(f_87, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 4.40/2.01  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.40/2.01  tff(f_46, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.40/2.01  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.40/2.01  tff(c_42, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.40/2.01  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.40/2.01  tff(c_76, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.40/2.01  tff(c_91, plain, (![B_38]: (k4_xboole_0(B_38, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_76])).
% 4.40/2.01  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.40/2.01  tff(c_96, plain, (![B_38]: (r1_tarski(k1_xboole_0, B_38))), inference(superposition, [status(thm), theory('equality')], [c_91, c_14])).
% 4.40/2.01  tff(c_52, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.40/2.01  tff(c_63, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 4.40/2.01  tff(c_18, plain, (![A_9]: (v1_zfmisc_1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.40/2.01  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.40/2.01  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.40/2.01  tff(c_344, plain, (![A_64, B_65]: ('#skF_1'(A_64, B_65)!=B_65 | v3_tex_2(B_65, A_64) | ~v2_tex_2(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.40/2.01  tff(c_347, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_344])).
% 4.40/2.01  tff(c_350, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_347])).
% 4.40/2.01  tff(c_351, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_63, c_350])).
% 4.40/2.01  tff(c_352, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_351])).
% 4.40/2.01  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.40/2.01  tff(c_46, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.40/2.01  tff(c_58, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.40/2.01  tff(c_64, plain, (v1_zfmisc_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_63, c_58])).
% 4.40/2.01  tff(c_1035, plain, (![B_93, A_94]: (v2_tex_2(B_93, A_94) | ~v1_zfmisc_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_94))) | v1_xboole_0(B_93) | ~l1_pre_topc(A_94) | ~v2_tdlat_3(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.40/2.01  tff(c_1038, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_1035])).
% 4.40/2.01  tff(c_1041, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_64, c_1038])).
% 4.40/2.01  tff(c_1043, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_352, c_1041])).
% 4.40/2.01  tff(c_1044, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_351])).
% 4.40/2.01  tff(c_1045, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_351])).
% 4.40/2.01  tff(c_1362, plain, (![B_106, A_107]: (r1_tarski(B_106, '#skF_1'(A_107, B_106)) | v3_tex_2(B_106, A_107) | ~v2_tex_2(B_106, A_107) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.40/2.01  tff(c_1364, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_1362])).
% 4.40/2.01  tff(c_1367, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1045, c_1364])).
% 4.40/2.01  tff(c_1368, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_63, c_1367])).
% 4.40/2.01  tff(c_34, plain, (![B_23, A_21]: (B_23=A_21 | ~r1_tarski(A_21, B_23) | ~v1_zfmisc_1(B_23) | v1_xboole_0(B_23) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.40/2.01  tff(c_1379, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1368, c_34])).
% 4.40/2.01  tff(c_1390, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_42, c_1044, c_1379])).
% 4.40/2.01  tff(c_1399, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1390])).
% 4.40/2.01  tff(c_1403, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_1399])).
% 4.40/2.01  tff(c_1240, plain, (![A_100, B_101]: (v2_tex_2('#skF_1'(A_100, B_101), A_100) | v3_tex_2(B_101, A_100) | ~v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.40/2.01  tff(c_1242, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_1240])).
% 4.40/2.01  tff(c_1245, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1045, c_1242])).
% 4.40/2.01  tff(c_1246, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_63, c_1245])).
% 4.40/2.01  tff(c_1892, plain, (![A_132, B_133]: (m1_subset_1('#skF_1'(A_132, B_133), k1_zfmisc_1(u1_struct_0(A_132))) | v3_tex_2(B_133, A_132) | ~v2_tex_2(B_133, A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.40/2.01  tff(c_38, plain, (![B_26, A_24]: (v1_zfmisc_1(B_26) | ~v2_tex_2(B_26, A_24) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | v1_xboole_0(B_26) | ~l1_pre_topc(A_24) | ~v2_tdlat_3(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.40/2.01  tff(c_2135, plain, (![A_168, B_169]: (v1_zfmisc_1('#skF_1'(A_168, B_169)) | ~v2_tex_2('#skF_1'(A_168, B_169), A_168) | v1_xboole_0('#skF_1'(A_168, B_169)) | ~v2_tdlat_3(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168) | v3_tex_2(B_169, A_168) | ~v2_tex_2(B_169, A_168) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168))), inference(resolution, [status(thm)], [c_1892, c_38])).
% 4.40/2.01  tff(c_2139, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1246, c_2135])).
% 4.40/2.01  tff(c_2143, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_1045, c_48, c_46, c_2139])).
% 4.40/2.01  tff(c_2145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_50, c_1403, c_1399, c_2143])).
% 4.40/2.01  tff(c_2146, plain, (v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1390])).
% 4.40/2.01  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.40/2.01  tff(c_72, plain, (![B_33, A_34]: (~v1_xboole_0(B_33) | B_33=A_34 | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.40/2.01  tff(c_75, plain, (![A_34]: (k1_xboole_0=A_34 | ~v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_2, c_72])).
% 4.40/2.01  tff(c_2156, plain, ('#skF_1'('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2146, c_75])).
% 4.40/2.01  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.40/2.01  tff(c_1381, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_1368, c_4])).
% 4.40/2.01  tff(c_1393, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1044, c_1381])).
% 4.40/2.01  tff(c_2164, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2156, c_1393])).
% 4.40/2.01  tff(c_2171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_2164])).
% 4.40/2.01  tff(c_2172, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 4.40/2.01  tff(c_2173, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 4.40/2.01  tff(c_2435, plain, (![B_197, A_198]: (v2_tex_2(B_197, A_198) | ~v3_tex_2(B_197, A_198) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.40/2.01  tff(c_2438, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_2435])).
% 4.40/2.01  tff(c_2441, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2173, c_2438])).
% 4.40/2.01  tff(c_2511, plain, (![B_216, A_217]: (v1_zfmisc_1(B_216) | ~v2_tex_2(B_216, A_217) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_217))) | v1_xboole_0(B_216) | ~l1_pre_topc(A_217) | ~v2_tdlat_3(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.40/2.01  tff(c_2517, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_2511])).
% 4.40/2.01  tff(c_2521, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_2441, c_2517])).
% 4.40/2.01  tff(c_2523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_2172, c_2521])).
% 4.40/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/2.01  
% 4.40/2.01  Inference rules
% 4.40/2.01  ----------------------
% 4.40/2.01  #Ref     : 0
% 4.40/2.01  #Sup     : 531
% 4.40/2.01  #Fact    : 6
% 4.40/2.01  #Define  : 0
% 4.40/2.01  #Split   : 12
% 4.40/2.01  #Chain   : 0
% 4.40/2.01  #Close   : 0
% 4.40/2.01  
% 4.40/2.01  Ordering : KBO
% 4.40/2.01  
% 4.40/2.01  Simplification rules
% 4.40/2.01  ----------------------
% 4.40/2.01  #Subsume      : 191
% 4.40/2.01  #Demod        : 358
% 4.40/2.01  #Tautology    : 240
% 4.40/2.01  #SimpNegUnit  : 140
% 4.40/2.01  #BackRed      : 7
% 4.40/2.01  
% 4.40/2.01  #Partial instantiations: 0
% 4.40/2.01  #Strategies tried      : 1
% 4.40/2.01  
% 4.40/2.01  Timing (in seconds)
% 4.40/2.01  ----------------------
% 4.40/2.02  Preprocessing        : 0.50
% 4.40/2.02  Parsing              : 0.27
% 4.40/2.02  CNF conversion       : 0.04
% 4.40/2.02  Main loop            : 0.70
% 4.40/2.02  Inferencing          : 0.24
% 4.40/2.02  Reduction            : 0.22
% 4.40/2.02  Demodulation         : 0.15
% 4.40/2.02  BG Simplification    : 0.03
% 4.40/2.02  Subsumption          : 0.16
% 4.40/2.02  Abstraction          : 0.03
% 4.40/2.02  MUC search           : 0.00
% 4.40/2.02  Cooper               : 0.00
% 4.40/2.02  Total                : 1.23
% 4.40/2.02  Index Insertion      : 0.00
% 4.40/2.02  Index Deletion       : 0.00
% 4.40/2.02  Index Matching       : 0.00
% 4.40/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
