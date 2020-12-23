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
% DateTime   : Thu Dec  3 10:29:05 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 389 expanded)
%              Number of leaves         :   36 ( 140 expanded)
%              Depth                    :   13
%              Number of atoms          :  305 (1050 expanded)
%              Number of equality atoms :   19 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_169,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_156,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_117,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_96,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1024,plain,(
    ! [A_165,B_166] :
      ( m1_pre_topc(k1_tex_2(A_165,B_166),A_165)
      | ~ m1_subset_1(B_166,u1_struct_0(A_165))
      | ~ l1_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1029,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1024])).

tff(c_1033,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1029])).

tff(c_1034,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1033])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1038,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1034,c_6])).

tff(c_1041,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1038])).

tff(c_856,plain,(
    ! [A_146,B_147] :
      ( ~ v2_struct_0(k1_tex_2(A_146,B_147))
      | ~ m1_subset_1(B_147,u1_struct_0(A_146))
      | ~ l1_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_863,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_856])).

tff(c_867,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_863])).

tff(c_868,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_867])).

tff(c_62,plain,
    ( v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_69,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_176,plain,(
    ! [A_67,B_68] :
      ( ~ v1_zfmisc_1(A_67)
      | ~ v1_subset_1(k6_domain_1(A_67,B_68),A_67)
      | ~ m1_subset_1(B_68,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_182,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_69,c_176])).

tff(c_185,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_182])).

tff(c_186,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_215,plain,(
    ! [A_73,B_74] :
      ( m1_pre_topc(k1_tex_2(A_73,B_74),A_73)
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_220,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_215])).

tff(c_224,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_220])).

tff(c_225,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_224])).

tff(c_307,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1('#skF_2'(A_78,B_79),k1_zfmisc_1(u1_struct_0(A_78)))
      | v1_tex_2(B_79,A_78)
      | ~ m1_pre_topc(B_79,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_32,plain,(
    ! [B_33,A_32] :
      ( v1_subset_1(B_33,A_32)
      | B_33 = A_32
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_684,plain,(
    ! [A_124,B_125] :
      ( v1_subset_1('#skF_2'(A_124,B_125),u1_struct_0(A_124))
      | u1_struct_0(A_124) = '#skF_2'(A_124,B_125)
      | v1_tex_2(B_125,A_124)
      | ~ m1_pre_topc(B_125,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_307,c_32])).

tff(c_26,plain,(
    ! [A_22,B_28] :
      ( ~ v1_subset_1('#skF_2'(A_22,B_28),u1_struct_0(A_22))
      | v1_tex_2(B_28,A_22)
      | ~ m1_pre_topc(B_28,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_703,plain,(
    ! [A_126,B_127] :
      ( u1_struct_0(A_126) = '#skF_2'(A_126,B_127)
      | v1_tex_2(B_127,A_126)
      | ~ m1_pre_topc(B_127,A_126)
      | ~ l1_pre_topc(A_126) ) ),
    inference(resolution,[status(thm)],[c_684,c_26])).

tff(c_56,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_149,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_56])).

tff(c_714,plain,
    ( '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_703,c_149])).

tff(c_721,plain,(
    '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_225,c_714])).

tff(c_229,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_225,c_6])).

tff(c_232,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_229])).

tff(c_163,plain,(
    ! [A_65,B_66] :
      ( ~ v2_struct_0(k1_tex_2(A_65,B_66))
      | ~ m1_subset_1(B_66,u1_struct_0(A_65))
      | ~ l1_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_170,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_163])).

tff(c_174,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_170])).

tff(c_175,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_174])).

tff(c_194,plain,(
    ! [B_69,A_70] :
      ( u1_struct_0(B_69) = '#skF_2'(A_70,B_69)
      | v1_tex_2(B_69,A_70)
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_197,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_149])).

tff(c_200,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_197])).

tff(c_235,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_200])).

tff(c_8,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_265,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_8])).

tff(c_291,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_265])).

tff(c_295,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_298,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_295])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_298])).

tff(c_304,plain,(
    l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_150,plain,(
    ! [A_63,B_64] :
      ( v7_struct_0(k1_tex_2(A_63,B_64))
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l1_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_157,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_150])).

tff(c_161,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_157])).

tff(c_162,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_161])).

tff(c_10,plain,(
    ! [A_9] :
      ( v1_zfmisc_1(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | ~ v7_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_268,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_10])).

tff(c_293,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_268])).

tff(c_306,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_293])).

tff(c_737,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_306])).

tff(c_741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_737])).

tff(c_742,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_746,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_742,c_8])).

tff(c_749,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_746])).

tff(c_752,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_749])).

tff(c_756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_752])).

tff(c_757,plain,(
    v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_797,plain,(
    ! [A_136,B_137] :
      ( v1_zfmisc_1(A_136)
      | k6_domain_1(A_136,B_137) != A_136
      | ~ m1_subset_1(B_137,A_136)
      | v1_xboole_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_809,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_797])).

tff(c_869,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') != u1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_809])).

tff(c_810,plain,(
    ! [A_138,B_139] :
      ( m1_subset_1(k6_domain_1(A_138,B_139),k1_zfmisc_1(A_138))
      | ~ m1_subset_1(B_139,A_138)
      | v1_xboole_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_922,plain,(
    ! [A_161,B_162] :
      ( v1_subset_1(k6_domain_1(A_161,B_162),A_161)
      | k6_domain_1(A_161,B_162) = A_161
      | ~ m1_subset_1(B_162,A_161)
      | v1_xboole_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_810,c_32])).

tff(c_758,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_928,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_922,c_758])).

tff(c_935,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_928])).

tff(c_936,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_869,c_935])).

tff(c_939,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_936,c_8])).

tff(c_942,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_939])).

tff(c_945,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_942])).

tff(c_949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_945])).

tff(c_951,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_809])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k6_domain_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_974,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_12])).

tff(c_980,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_974])).

tff(c_982,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_980])).

tff(c_985,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_982,c_8])).

tff(c_988,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_985])).

tff(c_991,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_988])).

tff(c_995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_991])).

tff(c_997,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_980])).

tff(c_950,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_809])).

tff(c_952,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_950])).

tff(c_14,plain,(
    ! [B_14,A_12] :
      ( m1_subset_1(u1_struct_0(B_14),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_pre_topc(B_14,A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1105,plain,(
    ! [B_181,A_182] :
      ( v1_subset_1(u1_struct_0(B_181),u1_struct_0(A_182))
      | ~ m1_subset_1(u1_struct_0(B_181),k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ v1_tex_2(B_181,A_182)
      | ~ m1_pre_topc(B_181,A_182)
      | ~ l1_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1121,plain,(
    ! [B_14,A_12] :
      ( v1_subset_1(u1_struct_0(B_14),u1_struct_0(A_12))
      | ~ v1_tex_2(B_14,A_12)
      | ~ m1_pre_topc(B_14,A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_1105])).

tff(c_953,plain,(
    ! [B_163,A_164] :
      ( ~ v1_subset_1(B_163,A_164)
      | v1_xboole_0(B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(A_164))
      | ~ v1_zfmisc_1(A_164)
      | v1_xboole_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1238,plain,(
    ! [B_206,A_207] :
      ( ~ v1_subset_1(u1_struct_0(B_206),u1_struct_0(A_207))
      | v1_xboole_0(u1_struct_0(B_206))
      | ~ v1_zfmisc_1(u1_struct_0(A_207))
      | v1_xboole_0(u1_struct_0(A_207))
      | ~ m1_pre_topc(B_206,A_207)
      | ~ l1_pre_topc(A_207) ) ),
    inference(resolution,[status(thm)],[c_14,c_953])).

tff(c_1247,plain,(
    ! [B_208,A_209] :
      ( v1_xboole_0(u1_struct_0(B_208))
      | ~ v1_zfmisc_1(u1_struct_0(A_209))
      | v1_xboole_0(u1_struct_0(A_209))
      | ~ v1_tex_2(B_208,A_209)
      | ~ m1_pre_topc(B_208,A_209)
      | ~ l1_pre_topc(A_209) ) ),
    inference(resolution,[status(thm)],[c_1121,c_1238])).

tff(c_1249,plain,(
    ! [B_208] :
      ( v1_xboole_0(u1_struct_0(B_208))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_208,'#skF_3')
      | ~ m1_pre_topc(B_208,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_952,c_1247])).

tff(c_1254,plain,(
    ! [B_208] :
      ( v1_xboole_0(u1_struct_0(B_208))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_208,'#skF_3')
      | ~ m1_pre_topc(B_208,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1249])).

tff(c_1262,plain,(
    ! [B_212] :
      ( v1_xboole_0(u1_struct_0(B_212))
      | ~ v1_tex_2(B_212,'#skF_3')
      | ~ m1_pre_topc(B_212,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_997,c_1254])).

tff(c_1277,plain,(
    ! [B_213] :
      ( ~ l1_struct_0(B_213)
      | v2_struct_0(B_213)
      | ~ v1_tex_2(B_213,'#skF_3')
      | ~ m1_pre_topc(B_213,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1262,c_8])).

tff(c_1284,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_757,c_1277])).

tff(c_1290,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_1284])).

tff(c_1291,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_868,c_1290])).

tff(c_1294,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_1291])).

tff(c_1298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_1294])).

tff(c_1299,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_950])).

tff(c_1318,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1299,c_8])).

tff(c_1321,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1318])).

tff(c_1324,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_1321])).

tff(c_1328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.67  
% 3.69/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.68  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.69/1.68  
% 3.69/1.68  %Foreground sorts:
% 3.69/1.68  
% 3.69/1.68  
% 3.69/1.68  %Background operators:
% 3.69/1.68  
% 3.69/1.68  
% 3.69/1.68  %Foreground operators:
% 3.69/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.69/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.68  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.69/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.69/1.68  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.69/1.68  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.69/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.69/1.68  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.69/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.68  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.69/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.69/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.68  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.69/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.69/1.68  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.69/1.68  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.69/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.69/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.69/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.68  
% 3.83/1.70  tff(f_169, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 3.83/1.70  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.83/1.70  tff(f_131, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.83/1.70  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.83/1.70  tff(f_145, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.83/1.70  tff(f_156, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.83/1.70  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 3.83/1.70  tff(f_117, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.83/1.70  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.83/1.70  tff(f_58, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.83/1.70  tff(f_96, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 3.83/1.70  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.83/1.70  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.83/1.70  tff(f_86, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.83/1.70  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.83/1.70  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.83/1.70  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.83/1.70  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.83/1.70  tff(c_1024, plain, (![A_165, B_166]: (m1_pre_topc(k1_tex_2(A_165, B_166), A_165) | ~m1_subset_1(B_166, u1_struct_0(A_165)) | ~l1_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.83/1.70  tff(c_1029, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1024])).
% 3.83/1.70  tff(c_1033, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1029])).
% 3.83/1.70  tff(c_1034, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_1033])).
% 3.83/1.70  tff(c_6, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.83/1.70  tff(c_1038, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1034, c_6])).
% 3.83/1.70  tff(c_1041, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1038])).
% 3.83/1.70  tff(c_856, plain, (![A_146, B_147]: (~v2_struct_0(k1_tex_2(A_146, B_147)) | ~m1_subset_1(B_147, u1_struct_0(A_146)) | ~l1_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.83/1.70  tff(c_863, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_856])).
% 3.83/1.70  tff(c_867, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_863])).
% 3.83/1.70  tff(c_868, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_867])).
% 3.83/1.70  tff(c_62, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.83/1.70  tff(c_69, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.83/1.70  tff(c_176, plain, (![A_67, B_68]: (~v1_zfmisc_1(A_67) | ~v1_subset_1(k6_domain_1(A_67, B_68), A_67) | ~m1_subset_1(B_68, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.83/1.70  tff(c_182, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_69, c_176])).
% 3.83/1.70  tff(c_185, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_182])).
% 3.83/1.70  tff(c_186, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_185])).
% 3.83/1.70  tff(c_215, plain, (![A_73, B_74]: (m1_pre_topc(k1_tex_2(A_73, B_74), A_73) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.83/1.70  tff(c_220, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_215])).
% 3.83/1.70  tff(c_224, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_220])).
% 3.83/1.70  tff(c_225, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_224])).
% 3.83/1.70  tff(c_307, plain, (![A_78, B_79]: (m1_subset_1('#skF_2'(A_78, B_79), k1_zfmisc_1(u1_struct_0(A_78))) | v1_tex_2(B_79, A_78) | ~m1_pre_topc(B_79, A_78) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.83/1.70  tff(c_32, plain, (![B_33, A_32]: (v1_subset_1(B_33, A_32) | B_33=A_32 | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.83/1.70  tff(c_684, plain, (![A_124, B_125]: (v1_subset_1('#skF_2'(A_124, B_125), u1_struct_0(A_124)) | u1_struct_0(A_124)='#skF_2'(A_124, B_125) | v1_tex_2(B_125, A_124) | ~m1_pre_topc(B_125, A_124) | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_307, c_32])).
% 3.83/1.70  tff(c_26, plain, (![A_22, B_28]: (~v1_subset_1('#skF_2'(A_22, B_28), u1_struct_0(A_22)) | v1_tex_2(B_28, A_22) | ~m1_pre_topc(B_28, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.83/1.70  tff(c_703, plain, (![A_126, B_127]: (u1_struct_0(A_126)='#skF_2'(A_126, B_127) | v1_tex_2(B_127, A_126) | ~m1_pre_topc(B_127, A_126) | ~l1_pre_topc(A_126))), inference(resolution, [status(thm)], [c_684, c_26])).
% 3.83/1.70  tff(c_56, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.83/1.70  tff(c_149, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_56])).
% 3.83/1.70  tff(c_714, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_703, c_149])).
% 3.83/1.70  tff(c_721, plain, ('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_225, c_714])).
% 3.83/1.70  tff(c_229, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_225, c_6])).
% 3.83/1.70  tff(c_232, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_229])).
% 3.83/1.70  tff(c_163, plain, (![A_65, B_66]: (~v2_struct_0(k1_tex_2(A_65, B_66)) | ~m1_subset_1(B_66, u1_struct_0(A_65)) | ~l1_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.83/1.70  tff(c_170, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_163])).
% 3.83/1.70  tff(c_174, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_170])).
% 3.83/1.70  tff(c_175, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_174])).
% 3.83/1.70  tff(c_194, plain, (![B_69, A_70]: (u1_struct_0(B_69)='#skF_2'(A_70, B_69) | v1_tex_2(B_69, A_70) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.83/1.70  tff(c_197, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_194, c_149])).
% 3.83/1.70  tff(c_200, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_197])).
% 3.83/1.70  tff(c_235, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_200])).
% 3.83/1.70  tff(c_8, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.83/1.70  tff(c_265, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_8])).
% 3.83/1.70  tff(c_291, plain, (~v1_xboole_0('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_175, c_265])).
% 3.83/1.70  tff(c_295, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_291])).
% 3.83/1.70  tff(c_298, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_295])).
% 3.83/1.70  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_298])).
% 3.83/1.70  tff(c_304, plain, (l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_291])).
% 3.83/1.70  tff(c_150, plain, (![A_63, B_64]: (v7_struct_0(k1_tex_2(A_63, B_64)) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l1_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.83/1.70  tff(c_157, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_150])).
% 3.83/1.70  tff(c_161, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_157])).
% 3.83/1.70  tff(c_162, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_161])).
% 3.83/1.70  tff(c_10, plain, (![A_9]: (v1_zfmisc_1(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | ~v7_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.83/1.70  tff(c_268, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_10])).
% 3.83/1.70  tff(c_293, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_268])).
% 3.83/1.70  tff(c_306, plain, (v1_zfmisc_1('#skF_2'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_293])).
% 3.83/1.70  tff(c_737, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_721, c_306])).
% 3.83/1.70  tff(c_741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_737])).
% 3.83/1.70  tff(c_742, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_185])).
% 3.83/1.70  tff(c_746, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_742, c_8])).
% 3.83/1.70  tff(c_749, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_746])).
% 3.83/1.70  tff(c_752, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_749])).
% 3.83/1.70  tff(c_756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_752])).
% 3.83/1.70  tff(c_757, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 3.83/1.70  tff(c_797, plain, (![A_136, B_137]: (v1_zfmisc_1(A_136) | k6_domain_1(A_136, B_137)!=A_136 | ~m1_subset_1(B_137, A_136) | v1_xboole_0(A_136))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.83/1.70  tff(c_809, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_797])).
% 3.83/1.70  tff(c_869, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')!=u1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_809])).
% 3.83/1.70  tff(c_810, plain, (![A_138, B_139]: (m1_subset_1(k6_domain_1(A_138, B_139), k1_zfmisc_1(A_138)) | ~m1_subset_1(B_139, A_138) | v1_xboole_0(A_138))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.83/1.70  tff(c_922, plain, (![A_161, B_162]: (v1_subset_1(k6_domain_1(A_161, B_162), A_161) | k6_domain_1(A_161, B_162)=A_161 | ~m1_subset_1(B_162, A_161) | v1_xboole_0(A_161))), inference(resolution, [status(thm)], [c_810, c_32])).
% 3.83/1.70  tff(c_758, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 3.83/1.70  tff(c_928, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_922, c_758])).
% 3.83/1.70  tff(c_935, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_928])).
% 3.83/1.70  tff(c_936, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_869, c_935])).
% 3.83/1.70  tff(c_939, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_936, c_8])).
% 3.83/1.70  tff(c_942, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_939])).
% 3.83/1.70  tff(c_945, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_942])).
% 3.83/1.70  tff(c_949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_945])).
% 3.83/1.70  tff(c_951, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_809])).
% 3.83/1.70  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(k6_domain_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.83/1.70  tff(c_974, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_951, c_12])).
% 3.83/1.70  tff(c_980, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_974])).
% 3.83/1.70  tff(c_982, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_980])).
% 3.83/1.70  tff(c_985, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_982, c_8])).
% 3.83/1.70  tff(c_988, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_985])).
% 3.83/1.70  tff(c_991, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_988])).
% 3.83/1.70  tff(c_995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_991])).
% 3.83/1.70  tff(c_997, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_980])).
% 3.83/1.70  tff(c_950, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_809])).
% 3.83/1.70  tff(c_952, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_950])).
% 3.83/1.70  tff(c_14, plain, (![B_14, A_12]: (m1_subset_1(u1_struct_0(B_14), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_pre_topc(B_14, A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.83/1.70  tff(c_1105, plain, (![B_181, A_182]: (v1_subset_1(u1_struct_0(B_181), u1_struct_0(A_182)) | ~m1_subset_1(u1_struct_0(B_181), k1_zfmisc_1(u1_struct_0(A_182))) | ~v1_tex_2(B_181, A_182) | ~m1_pre_topc(B_181, A_182) | ~l1_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.83/1.70  tff(c_1121, plain, (![B_14, A_12]: (v1_subset_1(u1_struct_0(B_14), u1_struct_0(A_12)) | ~v1_tex_2(B_14, A_12) | ~m1_pre_topc(B_14, A_12) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_14, c_1105])).
% 3.83/1.70  tff(c_953, plain, (![B_163, A_164]: (~v1_subset_1(B_163, A_164) | v1_xboole_0(B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(A_164)) | ~v1_zfmisc_1(A_164) | v1_xboole_0(A_164))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.83/1.70  tff(c_1238, plain, (![B_206, A_207]: (~v1_subset_1(u1_struct_0(B_206), u1_struct_0(A_207)) | v1_xboole_0(u1_struct_0(B_206)) | ~v1_zfmisc_1(u1_struct_0(A_207)) | v1_xboole_0(u1_struct_0(A_207)) | ~m1_pre_topc(B_206, A_207) | ~l1_pre_topc(A_207))), inference(resolution, [status(thm)], [c_14, c_953])).
% 3.83/1.70  tff(c_1247, plain, (![B_208, A_209]: (v1_xboole_0(u1_struct_0(B_208)) | ~v1_zfmisc_1(u1_struct_0(A_209)) | v1_xboole_0(u1_struct_0(A_209)) | ~v1_tex_2(B_208, A_209) | ~m1_pre_topc(B_208, A_209) | ~l1_pre_topc(A_209))), inference(resolution, [status(thm)], [c_1121, c_1238])).
% 3.83/1.70  tff(c_1249, plain, (![B_208]: (v1_xboole_0(u1_struct_0(B_208)) | v1_xboole_0(u1_struct_0('#skF_3')) | ~v1_tex_2(B_208, '#skF_3') | ~m1_pre_topc(B_208, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_952, c_1247])).
% 3.83/1.70  tff(c_1254, plain, (![B_208]: (v1_xboole_0(u1_struct_0(B_208)) | v1_xboole_0(u1_struct_0('#skF_3')) | ~v1_tex_2(B_208, '#skF_3') | ~m1_pre_topc(B_208, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1249])).
% 3.83/1.70  tff(c_1262, plain, (![B_212]: (v1_xboole_0(u1_struct_0(B_212)) | ~v1_tex_2(B_212, '#skF_3') | ~m1_pre_topc(B_212, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_997, c_1254])).
% 3.83/1.70  tff(c_1277, plain, (![B_213]: (~l1_struct_0(B_213) | v2_struct_0(B_213) | ~v1_tex_2(B_213, '#skF_3') | ~m1_pre_topc(B_213, '#skF_3'))), inference(resolution, [status(thm)], [c_1262, c_8])).
% 3.83/1.70  tff(c_1284, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_757, c_1277])).
% 3.83/1.70  tff(c_1290, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_1284])).
% 3.83/1.70  tff(c_1291, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_868, c_1290])).
% 3.83/1.70  tff(c_1294, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_1291])).
% 3.83/1.70  tff(c_1298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1041, c_1294])).
% 3.83/1.70  tff(c_1299, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_950])).
% 3.83/1.70  tff(c_1318, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1299, c_8])).
% 3.83/1.70  tff(c_1321, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_1318])).
% 3.83/1.70  tff(c_1324, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_1321])).
% 3.83/1.70  tff(c_1328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1324])).
% 3.83/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.70  
% 3.83/1.70  Inference rules
% 3.83/1.70  ----------------------
% 3.83/1.70  #Ref     : 0
% 3.83/1.70  #Sup     : 230
% 3.83/1.70  #Fact    : 0
% 3.83/1.70  #Define  : 0
% 3.83/1.70  #Split   : 14
% 3.83/1.70  #Chain   : 0
% 3.83/1.70  #Close   : 0
% 3.83/1.70  
% 3.83/1.70  Ordering : KBO
% 3.83/1.70  
% 3.83/1.70  Simplification rules
% 3.83/1.70  ----------------------
% 3.83/1.70  #Subsume      : 48
% 3.83/1.70  #Demod        : 137
% 3.83/1.70  #Tautology    : 31
% 3.83/1.70  #SimpNegUnit  : 45
% 3.83/1.70  #BackRed      : 20
% 3.83/1.70  
% 3.83/1.70  #Partial instantiations: 0
% 3.83/1.70  #Strategies tried      : 1
% 3.83/1.70  
% 3.83/1.70  Timing (in seconds)
% 3.83/1.70  ----------------------
% 3.83/1.70  Preprocessing        : 0.35
% 3.83/1.70  Parsing              : 0.19
% 3.83/1.70  CNF conversion       : 0.03
% 3.83/1.70  Main loop            : 0.50
% 3.83/1.70  Inferencing          : 0.19
% 3.83/1.70  Reduction            : 0.15
% 3.83/1.70  Demodulation         : 0.09
% 3.83/1.70  BG Simplification    : 0.03
% 3.83/1.70  Subsumption          : 0.09
% 3.83/1.70  Abstraction          : 0.03
% 3.83/1.70  MUC search           : 0.00
% 3.83/1.70  Cooper               : 0.00
% 3.83/1.70  Total                : 0.90
% 3.83/1.70  Index Insertion      : 0.00
% 3.83/1.70  Index Deletion       : 0.00
% 3.83/1.70  Index Matching       : 0.00
% 3.83/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
