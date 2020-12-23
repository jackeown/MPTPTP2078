%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:06 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 500 expanded)
%              Number of leaves         :   40 ( 183 expanded)
%              Depth                    :   12
%              Number of atoms          :  320 (1570 expanded)
%              Number of equality atoms :   35 ( 150 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_tops_1 > v1_subset_1 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k2_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_30,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_193,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_borsuk_1(B,A)
            & v1_tsep_1(B,A)
            & v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

tff(f_60,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_borsuk_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_129,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_118,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_143,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_175,axiom,(
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

tff(f_159,axiom,(
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

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : ~ v1_subset_1(k2_subset_1(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_67,plain,(
    ! [A_2] : ~ v1_subset_1(A_2,A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_54,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_740,plain,(
    ! [A_132,B_133] :
      ( m1_pre_topc(k1_pre_topc(A_132,B_133),A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_746,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_740])).

tff(c_750,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_746])).

tff(c_28,plain,(
    ! [B_21,A_19] :
      ( v1_borsuk_1(B_21,A_19)
      | ~ m1_pre_topc(B_21,A_19)
      | ~ l1_pre_topc(A_19)
      | ~ v1_tdlat_3(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_804,plain,(
    ! [A_142,B_143] :
      ( k2_pre_topc(A_142,B_143) = B_143
      | ~ v4_pre_topc(B_143,A_142)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_816,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_804])).

tff(c_820,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_816])).

tff(c_821,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_820])).

tff(c_705,plain,(
    ! [A_128,B_129] :
      ( u1_struct_0(k1_pre_topc(A_128,B_129)) = B_129
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_708,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_705])).

tff(c_711,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_708])).

tff(c_1034,plain,(
    ! [B_174,A_175] :
      ( v4_pre_topc(u1_struct_0(B_174),A_175)
      | ~ v1_borsuk_1(B_174,A_175)
      | ~ m1_subset_1(u1_struct_0(B_174),k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ m1_pre_topc(B_174,A_175)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1043,plain,(
    ! [A_175] :
      ( v4_pre_topc(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),A_175)
      | ~ v1_borsuk_1(k1_pre_topc('#skF_2','#skF_3'),A_175)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_175)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_1034])).

tff(c_1098,plain,(
    ! [A_182] :
      ( v4_pre_topc('#skF_3',A_182)
      | ~ v1_borsuk_1(k1_pre_topc('#skF_2','#skF_3'),A_182)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_182)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_1043])).

tff(c_1107,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ v1_borsuk_1(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1098])).

tff(c_1110,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ v1_borsuk_1(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_750,c_1107])).

tff(c_1111,plain,(
    ~ v1_borsuk_1(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_821,c_1110])).

tff(c_1114,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1111])).

tff(c_1117,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_750,c_1114])).

tff(c_1119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1117])).

tff(c_1120,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_820])).

tff(c_1127,plain,(
    ! [A_185,B_186] :
      ( k2_pre_topc(A_185,B_186) = u1_struct_0(A_185)
      | ~ v1_tops_1(B_186,A_185)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1139,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1127])).

tff(c_1144,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1120,c_1139])).

tff(c_1163,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1144])).

tff(c_785,plain,(
    ! [B_140,A_141] :
      ( v3_pre_topc(B_140,A_141)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ v1_tdlat_3(A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_797,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_785])).

tff(c_803,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_797])).

tff(c_66,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_79,plain,(
    ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_80,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_81,plain,(
    ! [B_44,A_45] :
      ( v1_subset_1(B_44,A_45)
      | B_44 = A_45
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_84,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_87,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_84])).

tff(c_89,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_50])).

tff(c_113,plain,(
    ! [A_50,B_51] :
      ( m1_pre_topc(k1_pre_topc(A_50,B_51),A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_115,plain,(
    ! [B_51] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_51),'#skF_2')
      | ~ m1_subset_1(B_51,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_113])).

tff(c_118,plain,(
    ! [B_52] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_52),'#skF_2')
      | ~ m1_subset_1(B_52,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_115])).

tff(c_122,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_118])).

tff(c_205,plain,(
    ! [A_64,B_65] :
      ( k2_pre_topc(A_64,B_65) = B_65
      | ~ v4_pre_topc(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_217,plain,(
    ! [B_65] :
      ( k2_pre_topc('#skF_2',B_65) = B_65
      | ~ v4_pre_topc(B_65,'#skF_2')
      | ~ m1_subset_1(B_65,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_205])).

tff(c_221,plain,(
    ! [B_66] :
      ( k2_pre_topc('#skF_2',B_66) = B_66
      | ~ v4_pre_topc(B_66,'#skF_2')
      | ~ m1_subset_1(B_66,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_217])).

tff(c_225,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_221])).

tff(c_226,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_123,plain,(
    ! [A_53,B_54] :
      ( u1_struct_0(k1_pre_topc(A_53,B_54)) = B_54
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,(
    ! [B_54] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_54)) = B_54
      | ~ m1_subset_1(B_54,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_123])).

tff(c_129,plain,(
    ! [B_55] :
      ( u1_struct_0(k1_pre_topc('#skF_2',B_55)) = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_126])).

tff(c_133,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_89,c_129])).

tff(c_472,plain,(
    ! [B_99,A_100] :
      ( v4_pre_topc(u1_struct_0(B_99),A_100)
      | ~ v1_borsuk_1(B_99,A_100)
      | ~ m1_subset_1(u1_struct_0(B_99),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_490,plain,(
    ! [B_99] :
      ( v4_pre_topc(u1_struct_0(B_99),'#skF_2')
      | ~ v1_borsuk_1(B_99,'#skF_2')
      | ~ m1_subset_1(u1_struct_0(B_99),k1_zfmisc_1('#skF_3'))
      | ~ m1_pre_topc(B_99,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_472])).

tff(c_495,plain,(
    ! [B_101] :
      ( v4_pre_topc(u1_struct_0(B_101),'#skF_2')
      | ~ v1_borsuk_1(B_101,'#skF_2')
      | ~ m1_subset_1(u1_struct_0(B_101),k1_zfmisc_1('#skF_3'))
      | ~ m1_pre_topc(B_101,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_490])).

tff(c_501,plain,
    ( v4_pre_topc(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),'#skF_2')
    | ~ v1_borsuk_1(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_495])).

tff(c_506,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ v1_borsuk_1(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_89,c_133,c_501])).

tff(c_507,plain,(
    ~ v1_borsuk_1(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_506])).

tff(c_513,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_507])).

tff(c_516,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_122,c_513])).

tff(c_518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_516])).

tff(c_519,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_550,plain,(
    ! [B_107,A_108] :
      ( v1_tops_1(B_107,A_108)
      | k2_pre_topc(A_108,B_107) != u1_struct_0(A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_562,plain,(
    ! [B_107] :
      ( v1_tops_1(B_107,'#skF_2')
      | k2_pre_topc('#skF_2',B_107) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_550])).

tff(c_567,plain,(
    ! [B_109] :
      ( v1_tops_1(B_109,'#skF_2')
      | k2_pre_topc('#skF_2',B_109) != '#skF_3'
      | ~ m1_subset_1(B_109,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_87,c_562])).

tff(c_570,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_89,c_567])).

tff(c_573,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_570])).

tff(c_634,plain,(
    ! [B_117,A_118] :
      ( v2_tex_2(B_117,A_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118)
      | ~ v1_tdlat_3(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_646,plain,(
    ! [B_117] :
      ( v2_tex_2(B_117,'#skF_2')
      | ~ m1_subset_1(B_117,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_634])).

tff(c_651,plain,(
    ! [B_117] :
      ( v2_tex_2(B_117,'#skF_2')
      | ~ m1_subset_1(B_117,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_646])).

tff(c_653,plain,(
    ! [B_119] :
      ( v2_tex_2(B_119,'#skF_2')
      | ~ m1_subset_1(B_119,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_651])).

tff(c_657,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_653])).

tff(c_658,plain,(
    ! [B_120,A_121] :
      ( v3_tex_2(B_120,A_121)
      | ~ v2_tex_2(B_120,A_121)
      | ~ v1_tops_1(B_120,A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_670,plain,(
    ! [B_120] :
      ( v3_tex_2(B_120,'#skF_2')
      | ~ v2_tex_2(B_120,'#skF_2')
      | ~ v1_tops_1(B_120,'#skF_2')
      | ~ m1_subset_1(B_120,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_658])).

tff(c_673,plain,(
    ! [B_120] :
      ( v3_tex_2(B_120,'#skF_2')
      | ~ v2_tex_2(B_120,'#skF_2')
      | ~ v1_tops_1(B_120,'#skF_2')
      | ~ m1_subset_1(B_120,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_670])).

tff(c_675,plain,(
    ! [B_122] :
      ( v3_tex_2(B_122,'#skF_2')
      | ~ v2_tex_2(B_122,'#skF_2')
      | ~ v1_tops_1(B_122,'#skF_2')
      | ~ m1_subset_1(B_122,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_673])).

tff(c_678,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_675])).

tff(c_681,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_657,c_678])).

tff(c_683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_681])).

tff(c_684,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_684])).

tff(c_687,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1281,plain,(
    ! [B_205,A_206] :
      ( v1_tops_1(B_205,A_206)
      | ~ v3_tex_2(B_205,A_206)
      | ~ v3_pre_topc(B_205,A_206)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_pre_topc(A_206)
      | ~ v2_pre_topc(A_206)
      | v2_struct_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1293,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1281])).

tff(c_1297,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_803,c_687,c_1293])).

tff(c_1299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1163,c_1297])).

tff(c_1300,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1144])).

tff(c_688,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1302,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1300,c_688])).

tff(c_1305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_1302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:32:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.68  
% 3.77/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.68  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_tops_1 > v1_subset_1 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k2_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 3.77/1.68  
% 3.77/1.68  %Foreground sorts:
% 3.77/1.68  
% 3.77/1.68  
% 3.77/1.68  %Background operators:
% 3.77/1.68  
% 3.77/1.68  
% 3.77/1.68  %Foreground operators:
% 3.77/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.77/1.68  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 3.77/1.68  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.77/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.68  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.77/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.77/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.77/1.68  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.77/1.68  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.77/1.68  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.77/1.68  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.77/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.68  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.77/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.68  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.77/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.68  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.77/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.68  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.77/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.77/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.77/1.68  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.77/1.68  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.77/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.68  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 3.77/1.68  
% 4.15/1.71  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.15/1.71  tff(f_30, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 4.15/1.71  tff(f_193, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 4.15/1.71  tff(f_38, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 4.15/1.71  tff(f_102, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 4.15/1.71  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.15/1.71  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 4.15/1.71  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tsep_1)).
% 4.15/1.71  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 4.15/1.71  tff(f_129, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 4.15/1.71  tff(f_118, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 4.15/1.71  tff(f_143, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 4.15/1.71  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 4.15/1.71  tff(f_159, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 4.15/1.71  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.15/1.71  tff(c_4, plain, (![A_2]: (~v1_subset_1(k2_subset_1(A_2), A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.15/1.71  tff(c_67, plain, (![A_2]: (~v1_subset_1(A_2, A_2))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.15/1.71  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.15/1.71  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.15/1.71  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.15/1.71  tff(c_54, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.15/1.71  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.15/1.71  tff(c_740, plain, (![A_132, B_133]: (m1_pre_topc(k1_pre_topc(A_132, B_133), A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.15/1.71  tff(c_746, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_740])).
% 4.15/1.71  tff(c_750, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_746])).
% 4.15/1.71  tff(c_28, plain, (![B_21, A_19]: (v1_borsuk_1(B_21, A_19) | ~m1_pre_topc(B_21, A_19) | ~l1_pre_topc(A_19) | ~v1_tdlat_3(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.15/1.71  tff(c_804, plain, (![A_142, B_143]: (k2_pre_topc(A_142, B_143)=B_143 | ~v4_pre_topc(B_143, A_142) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.15/1.71  tff(c_816, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_804])).
% 4.15/1.71  tff(c_820, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_816])).
% 4.15/1.71  tff(c_821, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_820])).
% 4.15/1.71  tff(c_705, plain, (![A_128, B_129]: (u1_struct_0(k1_pre_topc(A_128, B_129))=B_129 | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.15/1.71  tff(c_708, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_705])).
% 4.15/1.71  tff(c_711, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_708])).
% 4.15/1.71  tff(c_1034, plain, (![B_174, A_175]: (v4_pre_topc(u1_struct_0(B_174), A_175) | ~v1_borsuk_1(B_174, A_175) | ~m1_subset_1(u1_struct_0(B_174), k1_zfmisc_1(u1_struct_0(A_175))) | ~m1_pre_topc(B_174, A_175) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.15/1.71  tff(c_1043, plain, (![A_175]: (v4_pre_topc(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), A_175) | ~v1_borsuk_1(k1_pre_topc('#skF_2', '#skF_3'), A_175) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_175))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_175) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175))), inference(superposition, [status(thm), theory('equality')], [c_711, c_1034])).
% 4.15/1.71  tff(c_1098, plain, (![A_182]: (v4_pre_topc('#skF_3', A_182) | ~v1_borsuk_1(k1_pre_topc('#skF_2', '#skF_3'), A_182) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_182))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_182) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_711, c_1043])).
% 4.15/1.71  tff(c_1107, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~v1_borsuk_1(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1098])).
% 4.15/1.71  tff(c_1110, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~v1_borsuk_1(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_750, c_1107])).
% 4.15/1.71  tff(c_1111, plain, (~v1_borsuk_1(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_821, c_1110])).
% 4.15/1.71  tff(c_1114, plain, (~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1111])).
% 4.15/1.71  tff(c_1117, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_750, c_1114])).
% 4.15/1.71  tff(c_1119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1117])).
% 4.15/1.71  tff(c_1120, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_820])).
% 4.15/1.71  tff(c_1127, plain, (![A_185, B_186]: (k2_pre_topc(A_185, B_186)=u1_struct_0(A_185) | ~v1_tops_1(B_186, A_185) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.15/1.71  tff(c_1139, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1127])).
% 4.15/1.71  tff(c_1144, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1120, c_1139])).
% 4.15/1.71  tff(c_1163, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1144])).
% 4.15/1.71  tff(c_785, plain, (![B_140, A_141]: (v3_pre_topc(B_140, A_141) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~v1_tdlat_3(A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.15/1.71  tff(c_797, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_785])).
% 4.15/1.71  tff(c_803, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_797])).
% 4.15/1.71  tff(c_66, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.15/1.71  tff(c_79, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_66])).
% 4.15/1.71  tff(c_60, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.15/1.71  tff(c_80, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 4.15/1.71  tff(c_81, plain, (![B_44, A_45]: (v1_subset_1(B_44, A_45) | B_44=A_45 | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.15/1.71  tff(c_84, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_50, c_81])).
% 4.15/1.71  tff(c_87, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_79, c_84])).
% 4.15/1.71  tff(c_89, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_50])).
% 4.15/1.71  tff(c_113, plain, (![A_50, B_51]: (m1_pre_topc(k1_pre_topc(A_50, B_51), A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.15/1.71  tff(c_115, plain, (![B_51]: (m1_pre_topc(k1_pre_topc('#skF_2', B_51), '#skF_2') | ~m1_subset_1(B_51, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_113])).
% 4.15/1.71  tff(c_118, plain, (![B_52]: (m1_pre_topc(k1_pre_topc('#skF_2', B_52), '#skF_2') | ~m1_subset_1(B_52, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_115])).
% 4.15/1.71  tff(c_122, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_89, c_118])).
% 4.15/1.71  tff(c_205, plain, (![A_64, B_65]: (k2_pre_topc(A_64, B_65)=B_65 | ~v4_pre_topc(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.15/1.71  tff(c_217, plain, (![B_65]: (k2_pre_topc('#skF_2', B_65)=B_65 | ~v4_pre_topc(B_65, '#skF_2') | ~m1_subset_1(B_65, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_205])).
% 4.15/1.71  tff(c_221, plain, (![B_66]: (k2_pre_topc('#skF_2', B_66)=B_66 | ~v4_pre_topc(B_66, '#skF_2') | ~m1_subset_1(B_66, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_217])).
% 4.15/1.71  tff(c_225, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_89, c_221])).
% 4.15/1.71  tff(c_226, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_225])).
% 4.15/1.71  tff(c_123, plain, (![A_53, B_54]: (u1_struct_0(k1_pre_topc(A_53, B_54))=B_54 | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.15/1.71  tff(c_126, plain, (![B_54]: (u1_struct_0(k1_pre_topc('#skF_2', B_54))=B_54 | ~m1_subset_1(B_54, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_123])).
% 4.15/1.71  tff(c_129, plain, (![B_55]: (u1_struct_0(k1_pre_topc('#skF_2', B_55))=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_126])).
% 4.15/1.71  tff(c_133, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_89, c_129])).
% 4.15/1.71  tff(c_472, plain, (![B_99, A_100]: (v4_pre_topc(u1_struct_0(B_99), A_100) | ~v1_borsuk_1(B_99, A_100) | ~m1_subset_1(u1_struct_0(B_99), k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_pre_topc(B_99, A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.15/1.71  tff(c_490, plain, (![B_99]: (v4_pre_topc(u1_struct_0(B_99), '#skF_2') | ~v1_borsuk_1(B_99, '#skF_2') | ~m1_subset_1(u1_struct_0(B_99), k1_zfmisc_1('#skF_3')) | ~m1_pre_topc(B_99, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_472])).
% 4.15/1.71  tff(c_495, plain, (![B_101]: (v4_pre_topc(u1_struct_0(B_101), '#skF_2') | ~v1_borsuk_1(B_101, '#skF_2') | ~m1_subset_1(u1_struct_0(B_101), k1_zfmisc_1('#skF_3')) | ~m1_pre_topc(B_101, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_490])).
% 4.15/1.71  tff(c_501, plain, (v4_pre_topc(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), '#skF_2') | ~v1_borsuk_1(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_133, c_495])).
% 4.15/1.71  tff(c_506, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~v1_borsuk_1(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_89, c_133, c_501])).
% 4.15/1.71  tff(c_507, plain, (~v1_borsuk_1(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_226, c_506])).
% 4.15/1.71  tff(c_513, plain, (~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_507])).
% 4.15/1.71  tff(c_516, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_122, c_513])).
% 4.15/1.71  tff(c_518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_516])).
% 4.15/1.71  tff(c_519, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_225])).
% 4.15/1.71  tff(c_550, plain, (![B_107, A_108]: (v1_tops_1(B_107, A_108) | k2_pre_topc(A_108, B_107)!=u1_struct_0(A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.15/1.71  tff(c_562, plain, (![B_107]: (v1_tops_1(B_107, '#skF_2') | k2_pre_topc('#skF_2', B_107)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_550])).
% 4.15/1.71  tff(c_567, plain, (![B_109]: (v1_tops_1(B_109, '#skF_2') | k2_pre_topc('#skF_2', B_109)!='#skF_3' | ~m1_subset_1(B_109, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_87, c_562])).
% 4.15/1.71  tff(c_570, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_89, c_567])).
% 4.15/1.71  tff(c_573, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_570])).
% 4.15/1.71  tff(c_634, plain, (![B_117, A_118]: (v2_tex_2(B_117, A_118) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118) | ~v1_tdlat_3(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.15/1.71  tff(c_646, plain, (![B_117]: (v2_tex_2(B_117, '#skF_2') | ~m1_subset_1(B_117, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_634])).
% 4.15/1.71  tff(c_651, plain, (![B_117]: (v2_tex_2(B_117, '#skF_2') | ~m1_subset_1(B_117, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_646])).
% 4.15/1.71  tff(c_653, plain, (![B_119]: (v2_tex_2(B_119, '#skF_2') | ~m1_subset_1(B_119, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_651])).
% 4.15/1.71  tff(c_657, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_89, c_653])).
% 4.15/1.71  tff(c_658, plain, (![B_120, A_121]: (v3_tex_2(B_120, A_121) | ~v2_tex_2(B_120, A_121) | ~v1_tops_1(B_120, A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.15/1.71  tff(c_670, plain, (![B_120]: (v3_tex_2(B_120, '#skF_2') | ~v2_tex_2(B_120, '#skF_2') | ~v1_tops_1(B_120, '#skF_2') | ~m1_subset_1(B_120, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_87, c_658])).
% 4.15/1.71  tff(c_673, plain, (![B_120]: (v3_tex_2(B_120, '#skF_2') | ~v2_tex_2(B_120, '#skF_2') | ~v1_tops_1(B_120, '#skF_2') | ~m1_subset_1(B_120, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_670])).
% 4.15/1.71  tff(c_675, plain, (![B_122]: (v3_tex_2(B_122, '#skF_2') | ~v2_tex_2(B_122, '#skF_2') | ~v1_tops_1(B_122, '#skF_2') | ~m1_subset_1(B_122, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_673])).
% 4.15/1.71  tff(c_678, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_89, c_675])).
% 4.15/1.71  tff(c_681, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_657, c_678])).
% 4.15/1.71  tff(c_683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_681])).
% 4.15/1.71  tff(c_684, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_60])).
% 4.15/1.71  tff(c_686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_684])).
% 4.15/1.71  tff(c_687, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_66])).
% 4.15/1.71  tff(c_1281, plain, (![B_205, A_206]: (v1_tops_1(B_205, A_206) | ~v3_tex_2(B_205, A_206) | ~v3_pre_topc(B_205, A_206) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_206))) | ~l1_pre_topc(A_206) | ~v2_pre_topc(A_206) | v2_struct_0(A_206))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.15/1.71  tff(c_1293, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1281])).
% 4.15/1.71  tff(c_1297, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_803, c_687, c_1293])).
% 4.15/1.71  tff(c_1299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1163, c_1297])).
% 4.15/1.71  tff(c_1300, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1144])).
% 4.15/1.71  tff(c_688, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_66])).
% 4.15/1.71  tff(c_1302, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1300, c_688])).
% 4.15/1.71  tff(c_1305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_1302])).
% 4.15/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.71  
% 4.15/1.71  Inference rules
% 4.15/1.71  ----------------------
% 4.15/1.71  #Ref     : 0
% 4.15/1.71  #Sup     : 270
% 4.15/1.71  #Fact    : 0
% 4.15/1.71  #Define  : 0
% 4.15/1.71  #Split   : 10
% 4.15/1.71  #Chain   : 0
% 4.15/1.71  #Close   : 0
% 4.15/1.71  
% 4.15/1.71  Ordering : KBO
% 4.15/1.71  
% 4.15/1.71  Simplification rules
% 4.15/1.71  ----------------------
% 4.15/1.71  #Subsume      : 67
% 4.15/1.71  #Demod        : 194
% 4.15/1.71  #Tautology    : 51
% 4.15/1.71  #SimpNegUnit  : 33
% 4.15/1.71  #BackRed      : 4
% 4.15/1.71  
% 4.15/1.71  #Partial instantiations: 0
% 4.15/1.71  #Strategies tried      : 1
% 4.15/1.71  
% 4.15/1.71  Timing (in seconds)
% 4.15/1.71  ----------------------
% 4.15/1.71  Preprocessing        : 0.38
% 4.15/1.71  Parsing              : 0.20
% 4.15/1.71  CNF conversion       : 0.03
% 4.15/1.71  Main loop            : 0.50
% 4.15/1.71  Inferencing          : 0.18
% 4.15/1.71  Reduction            : 0.16
% 4.15/1.71  Demodulation         : 0.11
% 4.15/1.71  BG Simplification    : 0.03
% 4.15/1.71  Subsumption          : 0.09
% 4.15/1.71  Abstraction          : 0.02
% 4.15/1.71  MUC search           : 0.00
% 4.15/1.71  Cooper               : 0.00
% 4.15/1.71  Total                : 0.93
% 4.15/1.71  Index Insertion      : 0.00
% 4.15/1.71  Index Deletion       : 0.00
% 4.15/1.71  Index Matching       : 0.00
% 4.15/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
