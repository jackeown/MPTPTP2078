%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:07 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 867 expanded)
%              Number of leaves         :   43 ( 308 expanded)
%              Depth                    :   14
%              Number of atoms          :  323 (2194 expanded)
%              Number of equality atoms :   47 ( 342 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_173,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_76,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_98,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_155,axiom,(
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

tff(f_139,axiom,(
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

tff(c_12,plain,(
    ! [A_10] : ~ v1_subset_1(k2_subset_1(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_65,plain,(
    ! [A_10] : ~ v1_subset_1(A_10,A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_20,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1124,plain,(
    ! [A_170] :
      ( u1_struct_0(A_170) = k2_struct_0(A_170)
      | ~ l1_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1129,plain,(
    ! [A_171] :
      ( u1_struct_0(A_171) = k2_struct_0(A_171)
      | ~ l1_pre_topc(A_171) ) ),
    inference(resolution,[status(thm)],[c_20,c_1124])).

tff(c_1133,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1129])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1135,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1133,c_48])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_52,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1231,plain,(
    ! [B_189,A_190] :
      ( v3_pre_topc(B_189,A_190)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ v1_tdlat_3(A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1241,plain,(
    ! [B_189] :
      ( v3_pre_topc(B_189,'#skF_2')
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_1231])).

tff(c_1251,plain,(
    ! [B_191] :
      ( v3_pre_topc(B_191,'#skF_2')
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_52,c_1241])).

tff(c_1263,plain,(
    ! [B_6] :
      ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),B_6),'#skF_2')
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_1251])).

tff(c_1273,plain,(
    ! [A_194,B_195] :
      ( k2_pre_topc(A_194,B_195) = B_195
      | ~ v4_pre_topc(B_195,A_194)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1283,plain,(
    ! [B_195] :
      ( k2_pre_topc('#skF_2',B_195) = B_195
      | ~ v4_pre_topc(B_195,'#skF_2')
      | ~ m1_subset_1(B_195,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_1273])).

tff(c_1995,plain,(
    ! [B_275] :
      ( k2_pre_topc('#skF_2',B_275) = B_275
      | ~ v4_pre_topc(B_275,'#skF_2')
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1283])).

tff(c_2008,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1135,c_1995])).

tff(c_2017,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2008])).

tff(c_1159,plain,(
    ! [A_177,B_178] :
      ( k4_xboole_0(A_177,B_178) = k3_subset_1(A_177,B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(A_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1170,plain,(
    k4_xboole_0(k2_struct_0('#skF_2'),'#skF_3') = k3_subset_1(k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1135,c_1159])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_1185,plain,(
    ! [A_180,B_181,C_182] :
      ( k7_subset_1(A_180,B_181,C_182) = k4_xboole_0(B_181,C_182)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(A_180)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1194,plain,(
    ! [A_4,C_182] : k7_subset_1(A_4,A_4,C_182) = k4_xboole_0(A_4,C_182) ),
    inference(resolution,[status(thm)],[c_66,c_1185])).

tff(c_2224,plain,(
    ! [B_298,A_299] :
      ( v4_pre_topc(B_298,A_299)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_299),k2_struct_0(A_299),B_298),A_299)
      | ~ m1_subset_1(B_298,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ l1_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2227,plain,(
    ! [B_298] :
      ( v4_pre_topc(B_298,'#skF_2')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'),B_298),'#skF_2')
      | ~ m1_subset_1(B_298,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_2224])).

tff(c_2253,plain,(
    ! [B_303] :
      ( v4_pre_topc(B_303,'#skF_2')
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_2'),B_303),'#skF_2')
      | ~ m1_subset_1(B_303,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1133,c_1194,c_2227])).

tff(c_2263,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_2253])).

tff(c_2269,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1135,c_2263])).

tff(c_2270,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_2017,c_2269])).

tff(c_2275,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1263,c_2270])).

tff(c_2279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1135,c_2275])).

tff(c_2280,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2008])).

tff(c_1299,plain,(
    ! [A_197,B_198] :
      ( k2_pre_topc(A_197,B_198) = u1_struct_0(A_197)
      | ~ v1_tops_1(B_198,A_197)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1309,plain,(
    ! [B_198] :
      ( k2_pre_topc('#skF_2',B_198) = u1_struct_0('#skF_2')
      | ~ v1_tops_1(B_198,'#skF_2')
      | ~ m1_subset_1(B_198,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_1299])).

tff(c_2322,plain,(
    ! [B_308] :
      ( k2_pre_topc('#skF_2',B_308) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_308,'#skF_2')
      | ~ m1_subset_1(B_308,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1133,c_1309])).

tff(c_2329,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1135,c_2322])).

tff(c_2336,plain,
    ( k2_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_2329])).

tff(c_2340,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2336])).

tff(c_1264,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1135,c_1251])).

tff(c_58,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_79,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_81,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_86,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_20,c_81])).

tff(c_90,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_64,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_96,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_64])).

tff(c_97,plain,(
    ~ v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_96])).

tff(c_91,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_48])).

tff(c_98,plain,(
    ! [B_46,A_47] :
      ( v1_subset_1(B_46,A_47)
      | B_46 = A_47
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_101,plain,
    ( v1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_91,c_98])).

tff(c_107,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_101])).

tff(c_114,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_90])).

tff(c_182,plain,(
    ! [B_62,A_63] :
      ( v3_pre_topc(B_62,A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ v1_tdlat_3(A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_192,plain,(
    ! [B_62] :
      ( v3_pre_topc(B_62,'#skF_2')
      | ~ m1_subset_1(B_62,k1_zfmisc_1('#skF_3'))
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_182])).

tff(c_202,plain,(
    ! [B_64] :
      ( v3_pre_topc(B_64,'#skF_2')
      | ~ m1_subset_1(B_64,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_52,c_192])).

tff(c_211,plain,(
    ! [B_6] :
      ( v3_pre_topc(k3_subset_1('#skF_3',B_6),'#skF_2')
      | ~ m1_subset_1(B_6,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_202])).

tff(c_220,plain,(
    ! [A_67,B_68] :
      ( k2_pre_topc(A_67,B_68) = B_68
      | ~ v4_pre_topc(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_230,plain,(
    ! [B_68] :
      ( k2_pre_topc('#skF_2',B_68) = B_68
      | ~ v4_pre_topc(B_68,'#skF_2')
      | ~ m1_subset_1(B_68,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_220])).

tff(c_240,plain,(
    ! [B_69] :
      ( k2_pre_topc('#skF_2',B_69) = B_69
      | ~ v4_pre_topc(B_69,'#skF_2')
      | ~ m1_subset_1(B_69,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_230])).

tff(c_250,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_240])).

tff(c_271,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_130,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k3_subset_1(A_51,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_subset_1(A_4,A_4) ),
    inference(resolution,[status(thm)],[c_66,c_130])).

tff(c_148,plain,(
    ! [A_54,B_55,C_56] :
      ( k7_subset_1(A_54,B_55,C_56) = k4_xboole_0(B_55,C_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_154,plain,(
    ! [A_4,C_56] : k7_subset_1(A_4,A_4,C_56) = k4_xboole_0(A_4,C_56) ),
    inference(resolution,[status(thm)],[c_66,c_148])).

tff(c_547,plain,(
    ! [B_113,A_114] :
      ( v4_pre_topc(B_113,A_114)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_114),k2_struct_0(A_114),B_113),A_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_553,plain,(
    ! [B_113] :
      ( v4_pre_topc(B_113,'#skF_2')
      | ~ v3_pre_topc(k7_subset_1('#skF_3',k2_struct_0('#skF_2'),B_113),'#skF_2')
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_547])).

tff(c_583,plain,(
    ! [B_117] :
      ( v4_pre_topc(B_117,'#skF_2')
      | ~ v3_pre_topc(k4_xboole_0('#skF_3',B_117),'#skF_2')
      | ~ m1_subset_1(B_117,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_114,c_154,c_107,c_553])).

tff(c_594,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_pre_topc(k3_subset_1('#skF_3','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_583])).

tff(c_597,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_pre_topc(k3_subset_1('#skF_3','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_594])).

tff(c_598,plain,(
    ~ v3_pre_topc(k3_subset_1('#skF_3','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_597])).

tff(c_601,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_211,c_598])).

tff(c_605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_601])).

tff(c_606,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_646,plain,(
    ! [B_123,A_124] :
      ( v1_tops_1(B_123,A_124)
      | k2_pre_topc(A_124,B_123) != u1_struct_0(A_124)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_656,plain,(
    ! [B_123] :
      ( v1_tops_1(B_123,'#skF_2')
      | k2_pre_topc('#skF_2',B_123) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_123,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_646])).

tff(c_675,plain,(
    ! [B_126] :
      ( v1_tops_1(B_126,'#skF_2')
      | k2_pre_topc('#skF_2',B_126) != '#skF_3'
      | ~ m1_subset_1(B_126,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_114,c_656])).

tff(c_683,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_675])).

tff(c_687,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_683])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_772,plain,(
    ! [B_140,A_141] :
      ( v2_tex_2(B_140,A_141)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v1_tdlat_3(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_782,plain,(
    ! [B_140] :
      ( v2_tex_2(B_140,'#skF_2')
      | ~ m1_subset_1(B_140,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_772])).

tff(c_790,plain,(
    ! [B_140] :
      ( v2_tex_2(B_140,'#skF_2')
      | ~ m1_subset_1(B_140,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_782])).

tff(c_793,plain,(
    ! [B_142] :
      ( v2_tex_2(B_142,'#skF_2')
      | ~ m1_subset_1(B_142,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_790])).

tff(c_803,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_793])).

tff(c_1083,plain,(
    ! [B_166,A_167] :
      ( v3_tex_2(B_166,A_167)
      | ~ v2_tex_2(B_166,A_167)
      | ~ v1_tops_1(B_166,A_167)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1093,plain,(
    ! [B_166] :
      ( v3_tex_2(B_166,'#skF_2')
      | ~ v2_tex_2(B_166,'#skF_2')
      | ~ v1_tops_1(B_166,'#skF_2')
      | ~ m1_subset_1(B_166,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_1083])).

tff(c_1101,plain,(
    ! [B_166] :
      ( v3_tex_2(B_166,'#skF_2')
      | ~ v2_tex_2(B_166,'#skF_2')
      | ~ v1_tops_1(B_166,'#skF_2')
      | ~ m1_subset_1(B_166,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1093])).

tff(c_1104,plain,(
    ! [B_168] :
      ( v3_tex_2(B_168,'#skF_2')
      | ~ v2_tex_2(B_168,'#skF_2')
      | ~ v1_tops_1(B_168,'#skF_2')
      | ~ m1_subset_1(B_168,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1101])).

tff(c_1112,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1104])).

tff(c_1116,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_803,c_1112])).

tff(c_1118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_1116])).

tff(c_1120,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2757,plain,(
    ! [B_345,A_346] :
      ( v1_tops_1(B_345,A_346)
      | ~ v3_tex_2(B_345,A_346)
      | ~ v3_pre_topc(B_345,A_346)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2767,plain,(
    ! [B_345] :
      ( v1_tops_1(B_345,'#skF_2')
      | ~ v3_tex_2(B_345,'#skF_2')
      | ~ v3_pre_topc(B_345,'#skF_2')
      | ~ m1_subset_1(B_345,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_2757])).

tff(c_2775,plain,(
    ! [B_345] :
      ( v1_tops_1(B_345,'#skF_2')
      | ~ v3_tex_2(B_345,'#skF_2')
      | ~ v3_pre_topc(B_345,'#skF_2')
      | ~ m1_subset_1(B_345,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_2767])).

tff(c_2778,plain,(
    ! [B_347] :
      ( v1_tops_1(B_347,'#skF_2')
      | ~ v3_tex_2(B_347,'#skF_2')
      | ~ v3_pre_topc(B_347,'#skF_2')
      | ~ m1_subset_1(B_347,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2775])).

tff(c_2785,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1135,c_2778])).

tff(c_2793,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_1120,c_2785])).

tff(c_2795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2340,c_2793])).

tff(c_2796,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2336])).

tff(c_1119,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1134,plain,(
    v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1133,c_1119])).

tff(c_2809,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2796,c_1134])).

tff(c_2818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_2809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:22:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.64/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.85  
% 4.75/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.86  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 4.75/1.86  
% 4.75/1.86  %Foreground sorts:
% 4.75/1.86  
% 4.75/1.86  
% 4.75/1.86  %Background operators:
% 4.75/1.86  
% 4.75/1.86  
% 4.75/1.86  %Foreground operators:
% 4.75/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.75/1.86  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.75/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.75/1.86  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.75/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.75/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.75/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.75/1.86  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.75/1.86  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.75/1.86  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.75/1.86  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.75/1.86  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.75/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.75/1.86  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.75/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.75/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.75/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.75/1.86  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.75/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.75/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.75/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.75/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.75/1.86  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.75/1.86  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.75/1.86  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.75/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.75/1.86  
% 4.75/1.88  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.75/1.88  tff(f_44, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 4.75/1.88  tff(f_173, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 4.75/1.88  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.75/1.88  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.75/1.88  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.75/1.88  tff(f_109, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 4.75/1.88  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.75/1.88  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.75/1.88  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.75/1.88  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.75/1.88  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 4.75/1.88  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 4.75/1.88  tff(f_98, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 4.75/1.88  tff(f_123, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 4.75/1.88  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 4.75/1.88  tff(f_139, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 4.75/1.88  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.75/1.88  tff(c_12, plain, (![A_10]: (~v1_subset_1(k2_subset_1(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.75/1.88  tff(c_65, plain, (![A_10]: (~v1_subset_1(A_10, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 4.75/1.88  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.75/1.88  tff(c_20, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.75/1.88  tff(c_1124, plain, (![A_170]: (u1_struct_0(A_170)=k2_struct_0(A_170) | ~l1_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.75/1.88  tff(c_1129, plain, (![A_171]: (u1_struct_0(A_171)=k2_struct_0(A_171) | ~l1_pre_topc(A_171))), inference(resolution, [status(thm)], [c_20, c_1124])).
% 4.75/1.88  tff(c_1133, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1129])).
% 4.75/1.88  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.75/1.88  tff(c_1135, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1133, c_48])).
% 4.75/1.88  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.75/1.88  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.75/1.88  tff(c_52, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.75/1.88  tff(c_1231, plain, (![B_189, A_190]: (v3_pre_topc(B_189, A_190) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_190))) | ~v1_tdlat_3(A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.75/1.88  tff(c_1241, plain, (![B_189]: (v3_pre_topc(B_189, '#skF_2') | ~m1_subset_1(B_189, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1133, c_1231])).
% 4.75/1.88  tff(c_1251, plain, (![B_191]: (v3_pre_topc(B_191, '#skF_2') | ~m1_subset_1(B_191, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_52, c_1241])).
% 4.75/1.88  tff(c_1263, plain, (![B_6]: (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), B_6), '#skF_2') | ~m1_subset_1(B_6, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_1251])).
% 4.75/1.88  tff(c_1273, plain, (![A_194, B_195]: (k2_pre_topc(A_194, B_195)=B_195 | ~v4_pre_topc(B_195, A_194) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.75/1.88  tff(c_1283, plain, (![B_195]: (k2_pre_topc('#skF_2', B_195)=B_195 | ~v4_pre_topc(B_195, '#skF_2') | ~m1_subset_1(B_195, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1133, c_1273])).
% 4.75/1.88  tff(c_1995, plain, (![B_275]: (k2_pre_topc('#skF_2', B_275)=B_275 | ~v4_pre_topc(B_275, '#skF_2') | ~m1_subset_1(B_275, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1283])).
% 4.75/1.88  tff(c_2008, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1135, c_1995])).
% 4.75/1.88  tff(c_2017, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2008])).
% 4.75/1.88  tff(c_1159, plain, (![A_177, B_178]: (k4_xboole_0(A_177, B_178)=k3_subset_1(A_177, B_178) | ~m1_subset_1(B_178, k1_zfmisc_1(A_177)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.75/1.88  tff(c_1170, plain, (k4_xboole_0(k2_struct_0('#skF_2'), '#skF_3')=k3_subset_1(k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_1135, c_1159])).
% 4.75/1.88  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.75/1.88  tff(c_66, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 4.75/1.88  tff(c_1185, plain, (![A_180, B_181, C_182]: (k7_subset_1(A_180, B_181, C_182)=k4_xboole_0(B_181, C_182) | ~m1_subset_1(B_181, k1_zfmisc_1(A_180)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.75/1.88  tff(c_1194, plain, (![A_4, C_182]: (k7_subset_1(A_4, A_4, C_182)=k4_xboole_0(A_4, C_182))), inference(resolution, [status(thm)], [c_66, c_1185])).
% 4.75/1.88  tff(c_2224, plain, (![B_298, A_299]: (v4_pre_topc(B_298, A_299) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_299), k2_struct_0(A_299), B_298), A_299) | ~m1_subset_1(B_298, k1_zfmisc_1(u1_struct_0(A_299))) | ~l1_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.75/1.88  tff(c_2227, plain, (![B_298]: (v4_pre_topc(B_298, '#skF_2') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'), B_298), '#skF_2') | ~m1_subset_1(B_298, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1133, c_2224])).
% 4.75/1.88  tff(c_2253, plain, (![B_303]: (v4_pre_topc(B_303, '#skF_2') | ~v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_2'), B_303), '#skF_2') | ~m1_subset_1(B_303, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1133, c_1194, c_2227])).
% 4.75/1.88  tff(c_2263, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1170, c_2253])).
% 4.75/1.88  tff(c_2269, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1135, c_2263])).
% 4.75/1.88  tff(c_2270, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2017, c_2269])).
% 4.75/1.88  tff(c_2275, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1263, c_2270])).
% 4.75/1.88  tff(c_2279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1135, c_2275])).
% 4.75/1.88  tff(c_2280, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2008])).
% 4.75/1.88  tff(c_1299, plain, (![A_197, B_198]: (k2_pre_topc(A_197, B_198)=u1_struct_0(A_197) | ~v1_tops_1(B_198, A_197) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.75/1.88  tff(c_1309, plain, (![B_198]: (k2_pre_topc('#skF_2', B_198)=u1_struct_0('#skF_2') | ~v1_tops_1(B_198, '#skF_2') | ~m1_subset_1(B_198, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1133, c_1299])).
% 4.75/1.88  tff(c_2322, plain, (![B_308]: (k2_pre_topc('#skF_2', B_308)=k2_struct_0('#skF_2') | ~v1_tops_1(B_308, '#skF_2') | ~m1_subset_1(B_308, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1133, c_1309])).
% 4.75/1.88  tff(c_2329, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1135, c_2322])).
% 4.75/1.88  tff(c_2336, plain, (k2_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_2329])).
% 4.75/1.88  tff(c_2340, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2336])).
% 4.75/1.88  tff(c_1264, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1135, c_1251])).
% 4.75/1.88  tff(c_58, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.75/1.88  tff(c_79, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 4.75/1.88  tff(c_81, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.75/1.88  tff(c_86, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_20, c_81])).
% 4.75/1.88  tff(c_90, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_86])).
% 4.75/1.88  tff(c_64, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.75/1.88  tff(c_96, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_64])).
% 4.75/1.88  tff(c_97, plain, (~v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_79, c_96])).
% 4.75/1.88  tff(c_91, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_48])).
% 4.75/1.88  tff(c_98, plain, (![B_46, A_47]: (v1_subset_1(B_46, A_47) | B_46=A_47 | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.75/1.88  tff(c_101, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_91, c_98])).
% 4.75/1.88  tff(c_107, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_97, c_101])).
% 4.75/1.88  tff(c_114, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_90])).
% 4.75/1.88  tff(c_182, plain, (![B_62, A_63]: (v3_pre_topc(B_62, A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~v1_tdlat_3(A_63) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.75/1.88  tff(c_192, plain, (![B_62]: (v3_pre_topc(B_62, '#skF_2') | ~m1_subset_1(B_62, k1_zfmisc_1('#skF_3')) | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_182])).
% 4.75/1.88  tff(c_202, plain, (![B_64]: (v3_pre_topc(B_64, '#skF_2') | ~m1_subset_1(B_64, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_52, c_192])).
% 4.75/1.88  tff(c_211, plain, (![B_6]: (v3_pre_topc(k3_subset_1('#skF_3', B_6), '#skF_2') | ~m1_subset_1(B_6, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_202])).
% 4.75/1.88  tff(c_220, plain, (![A_67, B_68]: (k2_pre_topc(A_67, B_68)=B_68 | ~v4_pre_topc(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.75/1.88  tff(c_230, plain, (![B_68]: (k2_pre_topc('#skF_2', B_68)=B_68 | ~v4_pre_topc(B_68, '#skF_2') | ~m1_subset_1(B_68, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_220])).
% 4.75/1.88  tff(c_240, plain, (![B_69]: (k2_pre_topc('#skF_2', B_69)=B_69 | ~v4_pre_topc(B_69, '#skF_2') | ~m1_subset_1(B_69, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_230])).
% 4.75/1.88  tff(c_250, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_240])).
% 4.75/1.88  tff(c_271, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_250])).
% 4.75/1.88  tff(c_130, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k3_subset_1(A_51, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.75/1.88  tff(c_138, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_subset_1(A_4, A_4))), inference(resolution, [status(thm)], [c_66, c_130])).
% 4.75/1.88  tff(c_148, plain, (![A_54, B_55, C_56]: (k7_subset_1(A_54, B_55, C_56)=k4_xboole_0(B_55, C_56) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.75/1.88  tff(c_154, plain, (![A_4, C_56]: (k7_subset_1(A_4, A_4, C_56)=k4_xboole_0(A_4, C_56))), inference(resolution, [status(thm)], [c_66, c_148])).
% 4.75/1.88  tff(c_547, plain, (![B_113, A_114]: (v4_pre_topc(B_113, A_114) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_114), k2_struct_0(A_114), B_113), A_114) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.75/1.88  tff(c_553, plain, (![B_113]: (v4_pre_topc(B_113, '#skF_2') | ~v3_pre_topc(k7_subset_1('#skF_3', k2_struct_0('#skF_2'), B_113), '#skF_2') | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_547])).
% 4.75/1.88  tff(c_583, plain, (![B_117]: (v4_pre_topc(B_117, '#skF_2') | ~v3_pre_topc(k4_xboole_0('#skF_3', B_117), '#skF_2') | ~m1_subset_1(B_117, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_114, c_154, c_107, c_553])).
% 4.75/1.88  tff(c_594, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~v3_pre_topc(k3_subset_1('#skF_3', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_583])).
% 4.75/1.88  tff(c_597, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~v3_pre_topc(k3_subset_1('#skF_3', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_594])).
% 4.75/1.88  tff(c_598, plain, (~v3_pre_topc(k3_subset_1('#skF_3', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_271, c_597])).
% 4.75/1.88  tff(c_601, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_211, c_598])).
% 4.75/1.88  tff(c_605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_601])).
% 4.75/1.88  tff(c_606, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_250])).
% 4.75/1.88  tff(c_646, plain, (![B_123, A_124]: (v1_tops_1(B_123, A_124) | k2_pre_topc(A_124, B_123)!=u1_struct_0(A_124) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.75/1.88  tff(c_656, plain, (![B_123]: (v1_tops_1(B_123, '#skF_2') | k2_pre_topc('#skF_2', B_123)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_123, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_646])).
% 4.75/1.88  tff(c_675, plain, (![B_126]: (v1_tops_1(B_126, '#skF_2') | k2_pre_topc('#skF_2', B_126)!='#skF_3' | ~m1_subset_1(B_126, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_114, c_656])).
% 4.75/1.88  tff(c_683, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_66, c_675])).
% 4.75/1.88  tff(c_687, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_606, c_683])).
% 4.75/1.88  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.75/1.88  tff(c_772, plain, (![B_140, A_141]: (v2_tex_2(B_140, A_141) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141) | ~v1_tdlat_3(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.75/1.88  tff(c_782, plain, (![B_140]: (v2_tex_2(B_140, '#skF_2') | ~m1_subset_1(B_140, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_772])).
% 4.75/1.88  tff(c_790, plain, (![B_140]: (v2_tex_2(B_140, '#skF_2') | ~m1_subset_1(B_140, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_782])).
% 4.75/1.88  tff(c_793, plain, (![B_142]: (v2_tex_2(B_142, '#skF_2') | ~m1_subset_1(B_142, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_790])).
% 4.75/1.88  tff(c_803, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_793])).
% 4.75/1.88  tff(c_1083, plain, (![B_166, A_167]: (v3_tex_2(B_166, A_167) | ~v2_tex_2(B_166, A_167) | ~v1_tops_1(B_166, A_167) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.75/1.88  tff(c_1093, plain, (![B_166]: (v3_tex_2(B_166, '#skF_2') | ~v2_tex_2(B_166, '#skF_2') | ~v1_tops_1(B_166, '#skF_2') | ~m1_subset_1(B_166, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_1083])).
% 4.75/1.88  tff(c_1101, plain, (![B_166]: (v3_tex_2(B_166, '#skF_2') | ~v2_tex_2(B_166, '#skF_2') | ~v1_tops_1(B_166, '#skF_2') | ~m1_subset_1(B_166, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1093])).
% 4.75/1.88  tff(c_1104, plain, (![B_168]: (v3_tex_2(B_168, '#skF_2') | ~v2_tex_2(B_168, '#skF_2') | ~v1_tops_1(B_168, '#skF_2') | ~m1_subset_1(B_168, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1101])).
% 4.75/1.88  tff(c_1112, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1104])).
% 4.75/1.88  tff(c_1116, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_687, c_803, c_1112])).
% 4.75/1.88  tff(c_1118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_1116])).
% 4.75/1.88  tff(c_1120, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 4.75/1.88  tff(c_2757, plain, (![B_345, A_346]: (v1_tops_1(B_345, A_346) | ~v3_tex_2(B_345, A_346) | ~v3_pre_topc(B_345, A_346) | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_346))) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.75/1.88  tff(c_2767, plain, (![B_345]: (v1_tops_1(B_345, '#skF_2') | ~v3_tex_2(B_345, '#skF_2') | ~v3_pre_topc(B_345, '#skF_2') | ~m1_subset_1(B_345, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1133, c_2757])).
% 4.75/1.88  tff(c_2775, plain, (![B_345]: (v1_tops_1(B_345, '#skF_2') | ~v3_tex_2(B_345, '#skF_2') | ~v3_pre_topc(B_345, '#skF_2') | ~m1_subset_1(B_345, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_2767])).
% 4.75/1.88  tff(c_2778, plain, (![B_347]: (v1_tops_1(B_347, '#skF_2') | ~v3_tex_2(B_347, '#skF_2') | ~v3_pre_topc(B_347, '#skF_2') | ~m1_subset_1(B_347, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_2775])).
% 4.75/1.88  tff(c_2785, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1135, c_2778])).
% 4.75/1.88  tff(c_2793, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1264, c_1120, c_2785])).
% 4.75/1.88  tff(c_2795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2340, c_2793])).
% 4.75/1.88  tff(c_2796, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_2336])).
% 4.75/1.88  tff(c_1119, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_58])).
% 4.75/1.88  tff(c_1134, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1133, c_1119])).
% 4.75/1.88  tff(c_2809, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2796, c_1134])).
% 4.75/1.88  tff(c_2818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_2809])).
% 4.75/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.88  
% 4.75/1.88  Inference rules
% 4.75/1.88  ----------------------
% 4.75/1.88  #Ref     : 0
% 4.75/1.88  #Sup     : 544
% 4.75/1.88  #Fact    : 0
% 4.75/1.88  #Define  : 0
% 4.75/1.88  #Split   : 15
% 4.75/1.88  #Chain   : 0
% 4.75/1.88  #Close   : 0
% 4.75/1.88  
% 4.75/1.88  Ordering : KBO
% 4.75/1.88  
% 4.75/1.88  Simplification rules
% 4.75/1.88  ----------------------
% 4.75/1.88  #Subsume      : 40
% 4.75/1.88  #Demod        : 529
% 4.75/1.88  #Tautology    : 237
% 4.75/1.88  #SimpNegUnit  : 50
% 4.75/1.88  #BackRed      : 28
% 4.75/1.88  
% 4.75/1.88  #Partial instantiations: 0
% 4.75/1.88  #Strategies tried      : 1
% 4.75/1.88  
% 4.75/1.88  Timing (in seconds)
% 4.75/1.88  ----------------------
% 4.75/1.89  Preprocessing        : 0.35
% 4.75/1.89  Parsing              : 0.19
% 4.75/1.89  CNF conversion       : 0.02
% 4.75/1.89  Main loop            : 0.74
% 4.75/1.89  Inferencing          : 0.30
% 4.75/1.89  Reduction            : 0.22
% 4.75/1.89  Demodulation         : 0.15
% 4.75/1.89  BG Simplification    : 0.03
% 4.75/1.89  Subsumption          : 0.13
% 4.75/1.89  Abstraction          : 0.04
% 4.75/1.89  MUC search           : 0.00
% 4.75/1.89  Cooper               : 0.00
% 4.75/1.89  Total                : 1.14
% 4.75/1.89  Index Insertion      : 0.00
% 4.75/1.89  Index Deletion       : 0.00
% 4.75/1.89  Index Matching       : 0.00
% 4.75/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
