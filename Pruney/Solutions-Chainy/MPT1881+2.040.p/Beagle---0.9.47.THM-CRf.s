%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:11 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.31s
% Verified   : 
% Statistics : Number of formulae       :  148 (1533 expanded)
%              Number of leaves         :   37 ( 523 expanded)
%              Depth                    :   15
%              Number of atoms          :  325 (3971 expanded)
%              Number of equality atoms :   37 ( 639 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_65,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_61])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_38])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_42,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1045,plain,(
    ! [B_137,A_138] :
      ( v3_pre_topc(B_137,A_138)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ v1_tdlat_3(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1055,plain,(
    ! [B_137] :
      ( v3_pre_topc(B_137,'#skF_2')
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1045])).

tff(c_1060,plain,(
    ! [B_139] :
      ( v3_pre_topc(B_139,'#skF_2')
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_42,c_1055])).

tff(c_1068,plain,(
    ! [B_2] :
      ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),B_2),'#skF_2')
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_2,c_1060])).

tff(c_1030,plain,(
    ! [A_135,B_136] :
      ( k2_pre_topc(A_135,B_136) = B_136
      | ~ v4_pre_topc(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1040,plain,(
    ! [B_136] :
      ( k2_pre_topc('#skF_2',B_136) = B_136
      | ~ v4_pre_topc(B_136,'#skF_2')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1030])).

tff(c_1075,plain,(
    ! [B_141] :
      ( k2_pre_topc('#skF_2',B_141) = B_141
      | ~ v4_pre_topc(B_141,'#skF_2')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1040])).

tff(c_1084,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1075])).

tff(c_1085,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1084])).

tff(c_991,plain,(
    ! [A_127,B_128] :
      ( k3_subset_1(A_127,k3_subset_1(A_127,B_128)) = B_128
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_994,plain,(
    k3_subset_1(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_991])).

tff(c_1320,plain,(
    ! [A_166,B_167] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_166),B_167),A_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ v3_pre_topc(B_167,A_166)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1330,plain,(
    ! [B_167] :
      ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),B_167),'#skF_2')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_167,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1320])).

tff(c_1333,plain,(
    ! [B_168] :
      ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),B_168),'#skF_2')
      | ~ m1_subset_1(B_168,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_168,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_65,c_1330])).

tff(c_1340,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_1333])).

tff(c_1341,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1085,c_1340])).

tff(c_1342,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1341])).

tff(c_1345,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1068,c_1342])).

tff(c_1349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1345])).

tff(c_1350,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1341])).

tff(c_1368,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2,c_1350])).

tff(c_1372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1368])).

tff(c_1373,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1084])).

tff(c_1424,plain,(
    ! [A_172,B_173] :
      ( k2_pre_topc(A_172,B_173) = u1_struct_0(A_172)
      | ~ v1_tops_1(B_173,A_172)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1434,plain,(
    ! [B_173] :
      ( k2_pre_topc('#skF_2',B_173) = u1_struct_0('#skF_2')
      | ~ v1_tops_1(B_173,'#skF_2')
      | ~ m1_subset_1(B_173,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1424])).

tff(c_1439,plain,(
    ! [B_174] :
      ( k2_pre_topc('#skF_2',B_174) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_174,'#skF_2')
      | ~ m1_subset_1(B_174,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_65,c_1434])).

tff(c_1446,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1439])).

tff(c_1449,plain,
    ( k2_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1373,c_1446])).

tff(c_1450,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1449])).

tff(c_1069,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1060])).

tff(c_54,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_71,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_54])).

tff(c_72,plain,(
    ~ v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_48,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_74,plain,
    ( v1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_48])).

tff(c_75,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_74])).

tff(c_80,plain,(
    ! [B_37,A_38] :
      ( v1_subset_1(B_37,A_38)
      | B_37 = A_38
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_83,plain,
    ( v1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_80])).

tff(c_86,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_83])).

tff(c_87,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_66])).

tff(c_89,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_65])).

tff(c_184,plain,(
    ! [B_50,A_51] :
      ( v3_pre_topc(B_50,A_51)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ v1_tdlat_3(A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_194,plain,(
    ! [B_50] :
      ( v3_pre_topc(B_50,'#skF_2')
      | ~ m1_subset_1(B_50,k1_zfmisc_1('#skF_3'))
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_184])).

tff(c_199,plain,(
    ! [B_52] :
      ( v3_pre_topc(B_52,'#skF_2')
      | ~ m1_subset_1(B_52,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_42,c_194])).

tff(c_207,plain,(
    ! [B_2] :
      ( v3_pre_topc(k3_subset_1('#skF_3',B_2),'#skF_2')
      | ~ m1_subset_1(B_2,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2,c_199])).

tff(c_158,plain,(
    ! [A_47,B_48] :
      ( k2_pre_topc(A_47,B_48) = B_48
      | ~ v4_pre_topc(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_168,plain,(
    ! [B_48] :
      ( k2_pre_topc('#skF_2',B_48) = B_48
      | ~ v4_pre_topc(B_48,'#skF_2')
      | ~ m1_subset_1(B_48,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_158])).

tff(c_173,plain,(
    ! [B_49] :
      ( k2_pre_topc('#skF_2',B_49) = B_49
      | ~ v4_pre_topc(B_49,'#skF_2')
      | ~ m1_subset_1(B_49,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_168])).

tff(c_182,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_87,c_173])).

tff(c_183,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_123,plain,(
    ! [A_41,B_42] :
      ( k3_subset_1(A_41,k3_subset_1(A_41,B_42)) = B_42
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_129,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_87,c_123])).

tff(c_437,plain,(
    ! [A_74,B_75] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_74),B_75),A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ v3_pre_topc(B_75,A_74)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_447,plain,(
    ! [B_75] :
      ( v4_pre_topc(k3_subset_1('#skF_3',B_75),'#skF_2')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_75,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_437])).

tff(c_450,plain,(
    ! [B_76] :
      ( v4_pre_topc(k3_subset_1('#skF_3',B_76),'#skF_2')
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_3'))
      | ~ v3_pre_topc(B_76,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_89,c_447])).

tff(c_457,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_3'),k1_zfmisc_1('#skF_3'))
    | ~ v3_pre_topc(k3_subset_1('#skF_3','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_450])).

tff(c_458,plain,
    ( ~ m1_subset_1(k3_subset_1('#skF_3','#skF_3'),k1_zfmisc_1('#skF_3'))
    | ~ v3_pre_topc(k3_subset_1('#skF_3','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_457])).

tff(c_459,plain,(
    ~ v3_pre_topc(k3_subset_1('#skF_3','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_458])).

tff(c_462,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_207,c_459])).

tff(c_466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_462])).

tff(c_467,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3','#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_458])).

tff(c_485,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_467])).

tff(c_489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_485])).

tff(c_490,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_511,plain,(
    ! [B_80,A_81] :
      ( v1_tops_1(B_80,A_81)
      | k2_pre_topc(A_81,B_80) != u1_struct_0(A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_521,plain,(
    ! [B_80] :
      ( v1_tops_1(B_80,'#skF_2')
      | k2_pre_topc('#skF_2',B_80) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_80,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_511])).

tff(c_541,plain,(
    ! [B_84] :
      ( v1_tops_1(B_84,'#skF_2')
      | k2_pre_topc('#skF_2',B_84) != '#skF_3'
      | ~ m1_subset_1(B_84,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_89,c_521])).

tff(c_548,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_87,c_541])).

tff(c_552,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_548])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_631,plain,(
    ! [B_91,A_92] :
      ( v2_tex_2(B_91,A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v1_tdlat_3(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_641,plain,(
    ! [B_91] :
      ( v2_tex_2(B_91,'#skF_2')
      | ~ m1_subset_1(B_91,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_631])).

tff(c_645,plain,(
    ! [B_91] :
      ( v2_tex_2(B_91,'#skF_2')
      | ~ m1_subset_1(B_91,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_641])).

tff(c_647,plain,(
    ! [B_93] :
      ( v2_tex_2(B_93,'#skF_2')
      | ~ m1_subset_1(B_93,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_645])).

tff(c_656,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_87,c_647])).

tff(c_931,plain,(
    ! [B_120,A_121] :
      ( v3_tex_2(B_120,A_121)
      | ~ v2_tex_2(B_120,A_121)
      | ~ v1_tops_1(B_120,A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_941,plain,(
    ! [B_120] :
      ( v3_tex_2(B_120,'#skF_2')
      | ~ v2_tex_2(B_120,'#skF_2')
      | ~ v1_tops_1(B_120,'#skF_2')
      | ~ m1_subset_1(B_120,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_931])).

tff(c_945,plain,(
    ! [B_120] :
      ( v3_tex_2(B_120,'#skF_2')
      | ~ v2_tex_2(B_120,'#skF_2')
      | ~ v1_tops_1(B_120,'#skF_2')
      | ~ m1_subset_1(B_120,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_941])).

tff(c_947,plain,(
    ! [B_122] :
      ( v3_tex_2(B_122,'#skF_2')
      | ~ v2_tex_2(B_122,'#skF_2')
      | ~ v1_tops_1(B_122,'#skF_2')
      | ~ m1_subset_1(B_122,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_945])).

tff(c_954,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_87,c_947])).

tff(c_958,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_656,c_954])).

tff(c_960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_958])).

tff(c_961,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_1663,plain,(
    ! [B_200,A_201] :
      ( v1_tops_1(B_200,A_201)
      | ~ v3_tex_2(B_200,A_201)
      | ~ v3_pre_topc(B_200,A_201)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1673,plain,(
    ! [B_200] :
      ( v1_tops_1(B_200,'#skF_2')
      | ~ v3_tex_2(B_200,'#skF_2')
      | ~ v3_pre_topc(B_200,'#skF_2')
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1663])).

tff(c_1677,plain,(
    ! [B_200] :
      ( v1_tops_1(B_200,'#skF_2')
      | ~ v3_tex_2(B_200,'#skF_2')
      | ~ v3_pre_topc(B_200,'#skF_2')
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_1673])).

tff(c_1679,plain,(
    ! [B_202] :
      ( v1_tops_1(B_202,'#skF_2')
      | ~ v3_tex_2(B_202,'#skF_2')
      | ~ v3_pre_topc(B_202,'#skF_2')
      | ~ m1_subset_1(B_202,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1677])).

tff(c_1686,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1679])).

tff(c_1690,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1069,c_961,c_1686])).

tff(c_1692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1450,c_1690])).

tff(c_1693,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1449])).

tff(c_965,plain,(
    ! [A_123] :
      ( ~ v1_subset_1(k2_struct_0(A_123),u1_struct_0(A_123))
      | ~ l1_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_968,plain,
    ( ~ v1_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_965])).

tff(c_970,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_968])).

tff(c_973,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_970])).

tff(c_977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_973])).

tff(c_978,plain,(
    ~ v1_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_968])).

tff(c_1700,plain,(
    ~ v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_1693,c_978])).

tff(c_962,plain,(
    v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_1702,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_962])).

tff(c_1723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1700,c_1702])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.00/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.73  
% 4.00/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.73  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 4.00/1.73  
% 4.00/1.73  %Foreground sorts:
% 4.00/1.73  
% 4.00/1.73  
% 4.00/1.73  %Background operators:
% 4.00/1.73  
% 4.00/1.73  
% 4.00/1.73  %Foreground operators:
% 4.00/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.00/1.73  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.00/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/1.73  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.00/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.00/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.00/1.73  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.00/1.73  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.00/1.73  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.00/1.73  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.00/1.73  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.00/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.00/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.00/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.00/1.73  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.00/1.73  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.00/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.00/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.00/1.73  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.00/1.73  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.00/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.00/1.73  
% 4.31/1.76  tff(f_162, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 4.31/1.76  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.31/1.76  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.31/1.76  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.31/1.76  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 4.31/1.76  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.31/1.76  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.31/1.76  tff(f_71, axiom, (![A, B]: ((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_tops_1)).
% 4.31/1.76  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 4.31/1.76  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 4.31/1.76  tff(f_112, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 4.31/1.76  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 4.31/1.76  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 4.31/1.76  tff(f_46, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 4.31/1.76  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.31/1.76  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.31/1.76  tff(c_56, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.31/1.76  tff(c_61, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_8, c_56])).
% 4.31/1.76  tff(c_65, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_61])).
% 4.31/1.76  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.31/1.76  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_38])).
% 4.31/1.76  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.31/1.76  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.31/1.76  tff(c_42, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.31/1.76  tff(c_1045, plain, (![B_137, A_138]: (v3_pre_topc(B_137, A_138) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_138))) | ~v1_tdlat_3(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.31/1.76  tff(c_1055, plain, (![B_137]: (v3_pre_topc(B_137, '#skF_2') | ~m1_subset_1(B_137, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1045])).
% 4.31/1.76  tff(c_1060, plain, (![B_139]: (v3_pre_topc(B_139, '#skF_2') | ~m1_subset_1(B_139, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_42, c_1055])).
% 4.31/1.76  tff(c_1068, plain, (![B_2]: (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), B_2), '#skF_2') | ~m1_subset_1(B_2, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_2, c_1060])).
% 4.31/1.76  tff(c_1030, plain, (![A_135, B_136]: (k2_pre_topc(A_135, B_136)=B_136 | ~v4_pre_topc(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.31/1.76  tff(c_1040, plain, (![B_136]: (k2_pre_topc('#skF_2', B_136)=B_136 | ~v4_pre_topc(B_136, '#skF_2') | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1030])).
% 4.31/1.76  tff(c_1075, plain, (![B_141]: (k2_pre_topc('#skF_2', B_141)=B_141 | ~v4_pre_topc(B_141, '#skF_2') | ~m1_subset_1(B_141, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1040])).
% 4.31/1.76  tff(c_1084, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1075])).
% 4.31/1.76  tff(c_1085, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1084])).
% 4.31/1.76  tff(c_991, plain, (![A_127, B_128]: (k3_subset_1(A_127, k3_subset_1(A_127, B_128))=B_128 | ~m1_subset_1(B_128, k1_zfmisc_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.31/1.76  tff(c_994, plain, (k3_subset_1(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_66, c_991])).
% 4.31/1.76  tff(c_1320, plain, (![A_166, B_167]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_166), B_167), A_166) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~v3_pre_topc(B_167, A_166) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.31/1.76  tff(c_1330, plain, (![B_167]: (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), B_167), '#skF_2') | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_167, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1320])).
% 4.31/1.76  tff(c_1333, plain, (![B_168]: (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), B_168), '#skF_2') | ~m1_subset_1(B_168, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(B_168, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_65, c_1330])).
% 4.31/1.76  tff(c_1340, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_994, c_1333])).
% 4.31/1.76  tff(c_1341, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1085, c_1340])).
% 4.31/1.76  tff(c_1342, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1341])).
% 4.31/1.76  tff(c_1345, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1068, c_1342])).
% 4.31/1.76  tff(c_1349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_1345])).
% 4.31/1.76  tff(c_1350, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1341])).
% 4.31/1.76  tff(c_1368, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2, c_1350])).
% 4.31/1.76  tff(c_1372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_1368])).
% 4.31/1.76  tff(c_1373, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1084])).
% 4.31/1.76  tff(c_1424, plain, (![A_172, B_173]: (k2_pre_topc(A_172, B_173)=u1_struct_0(A_172) | ~v1_tops_1(B_173, A_172) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.31/1.76  tff(c_1434, plain, (![B_173]: (k2_pre_topc('#skF_2', B_173)=u1_struct_0('#skF_2') | ~v1_tops_1(B_173, '#skF_2') | ~m1_subset_1(B_173, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1424])).
% 4.31/1.76  tff(c_1439, plain, (![B_174]: (k2_pre_topc('#skF_2', B_174)=k2_struct_0('#skF_2') | ~v1_tops_1(B_174, '#skF_2') | ~m1_subset_1(B_174, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_65, c_1434])).
% 4.31/1.76  tff(c_1446, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1439])).
% 4.31/1.76  tff(c_1449, plain, (k2_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1373, c_1446])).
% 4.31/1.76  tff(c_1450, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1449])).
% 4.31/1.76  tff(c_1069, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1060])).
% 4.31/1.76  tff(c_54, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.31/1.76  tff(c_71, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_54])).
% 4.31/1.76  tff(c_72, plain, (~v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_71])).
% 4.31/1.76  tff(c_48, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.31/1.76  tff(c_74, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_48])).
% 4.31/1.76  tff(c_75, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_74])).
% 4.31/1.76  tff(c_80, plain, (![B_37, A_38]: (v1_subset_1(B_37, A_38) | B_37=A_38 | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.31/1.76  tff(c_83, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_66, c_80])).
% 4.31/1.76  tff(c_86, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_72, c_83])).
% 4.31/1.76  tff(c_87, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_66])).
% 4.31/1.76  tff(c_89, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_65])).
% 4.31/1.76  tff(c_184, plain, (![B_50, A_51]: (v3_pre_topc(B_50, A_51) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~v1_tdlat_3(A_51) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.31/1.76  tff(c_194, plain, (![B_50]: (v3_pre_topc(B_50, '#skF_2') | ~m1_subset_1(B_50, k1_zfmisc_1('#skF_3')) | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_184])).
% 4.31/1.76  tff(c_199, plain, (![B_52]: (v3_pre_topc(B_52, '#skF_2') | ~m1_subset_1(B_52, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_42, c_194])).
% 4.31/1.76  tff(c_207, plain, (![B_2]: (v3_pre_topc(k3_subset_1('#skF_3', B_2), '#skF_2') | ~m1_subset_1(B_2, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_2, c_199])).
% 4.31/1.76  tff(c_158, plain, (![A_47, B_48]: (k2_pre_topc(A_47, B_48)=B_48 | ~v4_pre_topc(B_48, A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.31/1.76  tff(c_168, plain, (![B_48]: (k2_pre_topc('#skF_2', B_48)=B_48 | ~v4_pre_topc(B_48, '#skF_2') | ~m1_subset_1(B_48, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_158])).
% 4.31/1.76  tff(c_173, plain, (![B_49]: (k2_pre_topc('#skF_2', B_49)=B_49 | ~v4_pre_topc(B_49, '#skF_2') | ~m1_subset_1(B_49, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_168])).
% 4.31/1.76  tff(c_182, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_87, c_173])).
% 4.31/1.76  tff(c_183, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_182])).
% 4.31/1.76  tff(c_123, plain, (![A_41, B_42]: (k3_subset_1(A_41, k3_subset_1(A_41, B_42))=B_42 | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.31/1.76  tff(c_129, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_87, c_123])).
% 4.31/1.76  tff(c_437, plain, (![A_74, B_75]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_74), B_75), A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~v3_pre_topc(B_75, A_74) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.31/1.76  tff(c_447, plain, (![B_75]: (v4_pre_topc(k3_subset_1('#skF_3', B_75), '#skF_2') | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_75, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_437])).
% 4.31/1.76  tff(c_450, plain, (![B_76]: (v4_pre_topc(k3_subset_1('#skF_3', B_76), '#skF_2') | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_3')) | ~v3_pre_topc(B_76, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_89, c_447])).
% 4.31/1.76  tff(c_457, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_3')) | ~v3_pre_topc(k3_subset_1('#skF_3', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_129, c_450])).
% 4.31/1.76  tff(c_458, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_3')) | ~v3_pre_topc(k3_subset_1('#skF_3', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_183, c_457])).
% 4.31/1.76  tff(c_459, plain, (~v3_pre_topc(k3_subset_1('#skF_3', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_458])).
% 4.31/1.76  tff(c_462, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_207, c_459])).
% 4.31/1.76  tff(c_466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_462])).
% 4.31/1.76  tff(c_467, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_3'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_458])).
% 4.31/1.76  tff(c_485, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_2, c_467])).
% 4.31/1.76  tff(c_489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_485])).
% 4.31/1.76  tff(c_490, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_182])).
% 4.31/1.76  tff(c_511, plain, (![B_80, A_81]: (v1_tops_1(B_80, A_81) | k2_pre_topc(A_81, B_80)!=u1_struct_0(A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.31/1.76  tff(c_521, plain, (![B_80]: (v1_tops_1(B_80, '#skF_2') | k2_pre_topc('#skF_2', B_80)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_80, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_511])).
% 4.31/1.76  tff(c_541, plain, (![B_84]: (v1_tops_1(B_84, '#skF_2') | k2_pre_topc('#skF_2', B_84)!='#skF_3' | ~m1_subset_1(B_84, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_89, c_521])).
% 4.31/1.76  tff(c_548, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_87, c_541])).
% 4.31/1.76  tff(c_552, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_490, c_548])).
% 4.31/1.76  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.31/1.76  tff(c_631, plain, (![B_91, A_92]: (v2_tex_2(B_91, A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v1_tdlat_3(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.31/1.76  tff(c_641, plain, (![B_91]: (v2_tex_2(B_91, '#skF_2') | ~m1_subset_1(B_91, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_631])).
% 4.31/1.76  tff(c_645, plain, (![B_91]: (v2_tex_2(B_91, '#skF_2') | ~m1_subset_1(B_91, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_641])).
% 4.31/1.76  tff(c_647, plain, (![B_93]: (v2_tex_2(B_93, '#skF_2') | ~m1_subset_1(B_93, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_645])).
% 4.31/1.76  tff(c_656, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_87, c_647])).
% 4.31/1.76  tff(c_931, plain, (![B_120, A_121]: (v3_tex_2(B_120, A_121) | ~v2_tex_2(B_120, A_121) | ~v1_tops_1(B_120, A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.31/1.76  tff(c_941, plain, (![B_120]: (v3_tex_2(B_120, '#skF_2') | ~v2_tex_2(B_120, '#skF_2') | ~v1_tops_1(B_120, '#skF_2') | ~m1_subset_1(B_120, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_931])).
% 4.31/1.76  tff(c_945, plain, (![B_120]: (v3_tex_2(B_120, '#skF_2') | ~v2_tex_2(B_120, '#skF_2') | ~v1_tops_1(B_120, '#skF_2') | ~m1_subset_1(B_120, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_941])).
% 4.31/1.76  tff(c_947, plain, (![B_122]: (v3_tex_2(B_122, '#skF_2') | ~v2_tex_2(B_122, '#skF_2') | ~v1_tops_1(B_122, '#skF_2') | ~m1_subset_1(B_122, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_46, c_945])).
% 4.31/1.76  tff(c_954, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_87, c_947])).
% 4.31/1.76  tff(c_958, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_552, c_656, c_954])).
% 4.31/1.76  tff(c_960, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_958])).
% 4.31/1.76  tff(c_961, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_71])).
% 4.31/1.76  tff(c_1663, plain, (![B_200, A_201]: (v1_tops_1(B_200, A_201) | ~v3_tex_2(B_200, A_201) | ~v3_pre_topc(B_200, A_201) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.31/1.76  tff(c_1673, plain, (![B_200]: (v1_tops_1(B_200, '#skF_2') | ~v3_tex_2(B_200, '#skF_2') | ~v3_pre_topc(B_200, '#skF_2') | ~m1_subset_1(B_200, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1663])).
% 4.31/1.76  tff(c_1677, plain, (![B_200]: (v1_tops_1(B_200, '#skF_2') | ~v3_tex_2(B_200, '#skF_2') | ~v3_pre_topc(B_200, '#skF_2') | ~m1_subset_1(B_200, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_1673])).
% 4.31/1.76  tff(c_1679, plain, (![B_202]: (v1_tops_1(B_202, '#skF_2') | ~v3_tex_2(B_202, '#skF_2') | ~v3_pre_topc(B_202, '#skF_2') | ~m1_subset_1(B_202, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_1677])).
% 4.31/1.76  tff(c_1686, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1679])).
% 4.31/1.76  tff(c_1690, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1069, c_961, c_1686])).
% 4.31/1.76  tff(c_1692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1450, c_1690])).
% 4.31/1.76  tff(c_1693, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1449])).
% 4.31/1.76  tff(c_965, plain, (![A_123]: (~v1_subset_1(k2_struct_0(A_123), u1_struct_0(A_123)) | ~l1_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.31/1.76  tff(c_968, plain, (~v1_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_65, c_965])).
% 4.31/1.76  tff(c_970, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_968])).
% 4.31/1.76  tff(c_973, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_970])).
% 4.31/1.76  tff(c_977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_973])).
% 4.31/1.76  tff(c_978, plain, (~v1_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_968])).
% 4.31/1.76  tff(c_1700, plain, (~v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_1693, c_978])).
% 4.31/1.76  tff(c_962, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_71])).
% 4.31/1.76  tff(c_1702, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_962])).
% 4.31/1.76  tff(c_1723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1700, c_1702])).
% 4.31/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.76  
% 4.31/1.76  Inference rules
% 4.31/1.76  ----------------------
% 4.31/1.76  #Ref     : 0
% 4.31/1.76  #Sup     : 345
% 4.31/1.76  #Fact    : 0
% 4.31/1.76  #Define  : 0
% 4.31/1.76  #Split   : 11
% 4.31/1.76  #Chain   : 0
% 4.31/1.76  #Close   : 0
% 4.31/1.76  
% 4.31/1.76  Ordering : KBO
% 4.31/1.76  
% 4.31/1.76  Simplification rules
% 4.31/1.76  ----------------------
% 4.31/1.76  #Subsume      : 43
% 4.31/1.76  #Demod        : 255
% 4.31/1.76  #Tautology    : 129
% 4.31/1.76  #SimpNegUnit  : 29
% 4.31/1.76  #BackRed      : 13
% 4.31/1.76  
% 4.31/1.76  #Partial instantiations: 0
% 4.31/1.76  #Strategies tried      : 1
% 4.31/1.76  
% 4.31/1.76  Timing (in seconds)
% 4.31/1.76  ----------------------
% 4.31/1.77  Preprocessing        : 0.35
% 4.31/1.77  Parsing              : 0.18
% 4.31/1.77  CNF conversion       : 0.02
% 4.31/1.77  Main loop            : 0.61
% 4.31/1.77  Inferencing          : 0.24
% 4.31/1.77  Reduction            : 0.18
% 4.31/1.77  Demodulation         : 0.12
% 4.31/1.77  BG Simplification    : 0.03
% 4.43/1.77  Subsumption          : 0.10
% 4.43/1.77  Abstraction          : 0.03
% 4.43/1.77  MUC search           : 0.00
% 4.43/1.77  Cooper               : 0.00
% 4.43/1.77  Total                : 1.02
% 4.43/1.77  Index Insertion      : 0.00
% 4.43/1.77  Index Deletion       : 0.00
% 4.43/1.77  Index Matching       : 0.00
% 4.43/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
