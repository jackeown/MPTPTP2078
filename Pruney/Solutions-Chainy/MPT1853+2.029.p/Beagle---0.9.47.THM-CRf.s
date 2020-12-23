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
% DateTime   : Thu Dec  3 10:29:04 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 224 expanded)
%              Number of leaves         :   32 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  242 ( 617 expanded)
%              Number of equality atoms :   11 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_177,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) )
           => ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc13_tex_2)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ~ ( u1_struct_0(B) = u1_struct_0(A)
              & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_164,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ~ v1_xboole_0(B)
           => ( ~ v1_xboole_0(B)
              & ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_70,plain,(
    ! [A_41,B_42] :
      ( ~ v2_struct_0(k1_tex_2(A_41,B_42))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_73,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_70])).

tff(c_76,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_73])).

tff(c_77,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_76])).

tff(c_97,plain,(
    ! [A_49,B_50] :
      ( m1_pre_topc(k1_tex_2(A_49,B_50),A_49)
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_99,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_97])).

tff(c_102,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_99])).

tff(c_103,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_102])).

tff(c_88,plain,(
    ! [A_45,B_46] :
      ( v7_struct_0(k1_tex_2(A_45,B_46))
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_91,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_88])).

tff(c_94,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_91])).

tff(c_95,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_94])).

tff(c_117,plain,(
    ! [B_53,A_54] :
      ( ~ v7_struct_0(B_53)
      | v1_tex_2(B_53,A_54)
      | v2_struct_0(B_53)
      | ~ m1_pre_topc(B_53,A_54)
      | ~ l1_pre_topc(A_54)
      | v7_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,
    ( v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_68,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_87,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_46])).

tff(c_123,plain,
    ( ~ v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_117,c_87])).

tff(c_127,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_103,c_95,c_123])).

tff(c_128,plain,(
    v7_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_77,c_127])).

tff(c_135,plain,(
    ! [A_59,B_60] :
      ( ~ v7_struct_0(A_59)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_59),B_60),u1_struct_0(A_59))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_struct_0(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_141,plain,
    ( ~ v7_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_135])).

tff(c_145,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_128,c_141])).

tff(c_146,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_145])).

tff(c_149,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_146])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_149])).

tff(c_154,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_183,plain,(
    ! [B_68,A_69] :
      ( ~ v1_tex_2(B_68,A_69)
      | u1_struct_0(B_68) != u1_struct_0(A_69)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_186,plain,
    ( u1_struct_0(k1_tex_2('#skF_1','#skF_2')) != u1_struct_0('#skF_1')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_154,c_183])).

tff(c_189,plain,
    ( u1_struct_0(k1_tex_2('#skF_1','#skF_2')) != u1_struct_0('#skF_1')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_186])).

tff(c_190,plain,(
    ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_191,plain,(
    ! [A_70,B_71] :
      ( m1_pre_topc(k1_tex_2(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,u1_struct_0(A_70))
      | ~ l1_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_193,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_191])).

tff(c_196,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_193])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_190,c_196])).

tff(c_200,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_203,plain,
    ( l1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_200,c_4])).

tff(c_206,plain,(
    l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_203])).

tff(c_157,plain,(
    ! [A_62,B_63] :
      ( ~ v2_struct_0(k1_tex_2(A_62,B_63))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_160,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_157])).

tff(c_163,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_160])).

tff(c_164,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_163])).

tff(c_199,plain,(
    u1_struct_0(k1_tex_2('#skF_1','#skF_2')) != u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_226,plain,(
    ! [A_78,B_79] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(A_78),B_79),u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l1_struct_0(A_78)
      | v7_struct_0(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_155,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_229,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_226,c_155])).

tff(c_232,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_229])).

tff(c_233,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_232])).

tff(c_234,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_237,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_234])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_237])).

tff(c_242,plain,(
    v7_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_243,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_58,plain,(
    ! [B_38,A_39] :
      ( m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_pre_topc(B_38,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( v1_subset_1(B_16,A_15)
      | B_16 = A_15
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_66,plain,(
    ! [B_38,A_39] :
      ( v1_subset_1(u1_struct_0(B_38),u1_struct_0(A_39))
      | u1_struct_0(B_38) = u1_struct_0(A_39)
      | ~ m1_pre_topc(B_38,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_58,c_18])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( m1_subset_1(u1_struct_0(B_8),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_pre_topc(B_8,A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_249,plain,(
    ! [B_82,A_83] :
      ( ~ v1_subset_1(B_82,u1_struct_0(A_83))
      | v1_xboole_0(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_struct_0(A_83)
      | ~ v7_struct_0(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_262,plain,(
    ! [B_86,A_87] :
      ( ~ v1_subset_1(u1_struct_0(B_86),u1_struct_0(A_87))
      | v1_xboole_0(u1_struct_0(B_86))
      | ~ l1_struct_0(A_87)
      | ~ v7_struct_0(A_87)
      | v2_struct_0(A_87)
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_8,c_249])).

tff(c_267,plain,(
    ! [B_88,A_89] :
      ( v1_xboole_0(u1_struct_0(B_88))
      | ~ l1_struct_0(A_89)
      | ~ v7_struct_0(A_89)
      | v2_struct_0(A_89)
      | u1_struct_0(B_88) = u1_struct_0(A_89)
      | ~ m1_pre_topc(B_88,A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_66,c_262])).

tff(c_269,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_1','#skF_2')))
    | ~ l1_struct_0('#skF_1')
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1')
    | u1_struct_0(k1_tex_2('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_200,c_267])).

tff(c_272,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_1','#skF_2')))
    | v2_struct_0('#skF_1')
    | u1_struct_0(k1_tex_2('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_242,c_243,c_269])).

tff(c_273,plain,(
    v1_xboole_0(u1_struct_0(k1_tex_2('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_44,c_272])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_276,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_273,c_6])).

tff(c_279,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_276])).

tff(c_282,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_279])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_282])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.29  
% 2.38/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.29  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.38/1.29  
% 2.38/1.29  %Foreground sorts:
% 2.38/1.29  
% 2.38/1.29  
% 2.38/1.29  %Background operators:
% 2.38/1.29  
% 2.38/1.29  
% 2.38/1.29  %Foreground operators:
% 2.38/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.38/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.29  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.38/1.29  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.38/1.29  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.38/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.38/1.29  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.38/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.29  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.38/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.38/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.29  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.38/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.38/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.38/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.29  
% 2.38/1.31  tff(f_177, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 2.38/1.31  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.38/1.31  tff(f_128, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.38/1.31  tff(f_114, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.38/1.31  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v1_tex_2(B, A)) => (~v2_struct_0(B) & ~v7_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc13_tex_2)).
% 2.38/1.31  tff(f_151, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 2.38/1.31  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 2.38/1.31  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.38/1.31  tff(f_164, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tex_2)).
% 2.38/1.31  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.38/1.31  tff(f_100, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.38/1.31  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~v1_xboole_0(B) => (~v1_xboole_0(B) & ~v1_subset_1(B, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tex_2)).
% 2.38/1.31  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.38/1.31  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 2.38/1.31  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 2.38/1.31  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.38/1.31  tff(c_40, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 2.38/1.31  tff(c_70, plain, (![A_41, B_42]: (~v2_struct_0(k1_tex_2(A_41, B_42)) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.38/1.31  tff(c_73, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_70])).
% 2.38/1.31  tff(c_76, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_73])).
% 2.38/1.31  tff(c_77, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_76])).
% 2.38/1.31  tff(c_97, plain, (![A_49, B_50]: (m1_pre_topc(k1_tex_2(A_49, B_50), A_49) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.38/1.31  tff(c_99, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_97])).
% 2.38/1.31  tff(c_102, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_99])).
% 2.38/1.31  tff(c_103, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_102])).
% 2.38/1.31  tff(c_88, plain, (![A_45, B_46]: (v7_struct_0(k1_tex_2(A_45, B_46)) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.38/1.31  tff(c_91, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_88])).
% 2.38/1.31  tff(c_94, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_91])).
% 2.38/1.31  tff(c_95, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_94])).
% 2.38/1.31  tff(c_117, plain, (![B_53, A_54]: (~v7_struct_0(B_53) | v1_tex_2(B_53, A_54) | v2_struct_0(B_53) | ~m1_pre_topc(B_53, A_54) | ~l1_pre_topc(A_54) | v7_struct_0(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.38/1.31  tff(c_52, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 2.38/1.31  tff(c_68, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_52])).
% 2.38/1.31  tff(c_46, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1')) | ~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 2.38/1.31  tff(c_87, plain, (~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_46])).
% 2.38/1.31  tff(c_123, plain, (~v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_117, c_87])).
% 2.38/1.31  tff(c_127, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_103, c_95, c_123])).
% 2.38/1.31  tff(c_128, plain, (v7_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_77, c_127])).
% 2.38/1.31  tff(c_135, plain, (![A_59, B_60]: (~v7_struct_0(A_59) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_59), B_60), u1_struct_0(A_59)) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_struct_0(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.38/1.31  tff(c_141, plain, (~v7_struct_0('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_135])).
% 2.38/1.31  tff(c_145, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_128, c_141])).
% 2.38/1.31  tff(c_146, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_145])).
% 2.38/1.31  tff(c_149, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_146])).
% 2.38/1.31  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_149])).
% 2.38/1.31  tff(c_154, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 2.38/1.31  tff(c_183, plain, (![B_68, A_69]: (~v1_tex_2(B_68, A_69) | u1_struct_0(B_68)!=u1_struct_0(A_69) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.38/1.31  tff(c_186, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))!=u1_struct_0('#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_154, c_183])).
% 2.38/1.31  tff(c_189, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))!=u1_struct_0('#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_186])).
% 2.38/1.31  tff(c_190, plain, (~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_189])).
% 2.38/1.31  tff(c_191, plain, (![A_70, B_71]: (m1_pre_topc(k1_tex_2(A_70, B_71), A_70) | ~m1_subset_1(B_71, u1_struct_0(A_70)) | ~l1_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.38/1.31  tff(c_193, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_191])).
% 2.38/1.31  tff(c_196, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_193])).
% 2.38/1.31  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_190, c_196])).
% 2.38/1.31  tff(c_200, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_189])).
% 2.38/1.31  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.31  tff(c_203, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_200, c_4])).
% 2.38/1.31  tff(c_206, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_203])).
% 2.38/1.31  tff(c_157, plain, (![A_62, B_63]: (~v2_struct_0(k1_tex_2(A_62, B_63)) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.38/1.31  tff(c_160, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_157])).
% 2.38/1.31  tff(c_163, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_160])).
% 2.38/1.31  tff(c_164, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_163])).
% 2.38/1.31  tff(c_199, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))!=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_189])).
% 2.38/1.31  tff(c_226, plain, (![A_78, B_79]: (v1_subset_1(k6_domain_1(u1_struct_0(A_78), B_79), u1_struct_0(A_78)) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~l1_struct_0(A_78) | v7_struct_0(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.38/1.31  tff(c_155, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_52])).
% 2.38/1.31  tff(c_229, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_226, c_155])).
% 2.38/1.31  tff(c_232, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_229])).
% 2.38/1.31  tff(c_233, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_232])).
% 2.38/1.31  tff(c_234, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_233])).
% 2.38/1.31  tff(c_237, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_234])).
% 2.38/1.31  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_237])).
% 2.38/1.31  tff(c_242, plain, (v7_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_233])).
% 2.38/1.31  tff(c_243, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_233])).
% 2.38/1.31  tff(c_58, plain, (![B_38, A_39]: (m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_pre_topc(B_38, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.38/1.31  tff(c_18, plain, (![B_16, A_15]: (v1_subset_1(B_16, A_15) | B_16=A_15 | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.38/1.31  tff(c_66, plain, (![B_38, A_39]: (v1_subset_1(u1_struct_0(B_38), u1_struct_0(A_39)) | u1_struct_0(B_38)=u1_struct_0(A_39) | ~m1_pre_topc(B_38, A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_58, c_18])).
% 2.38/1.31  tff(c_8, plain, (![B_8, A_6]: (m1_subset_1(u1_struct_0(B_8), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_pre_topc(B_8, A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.38/1.31  tff(c_249, plain, (![B_82, A_83]: (~v1_subset_1(B_82, u1_struct_0(A_83)) | v1_xboole_0(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_struct_0(A_83) | ~v7_struct_0(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.38/1.31  tff(c_262, plain, (![B_86, A_87]: (~v1_subset_1(u1_struct_0(B_86), u1_struct_0(A_87)) | v1_xboole_0(u1_struct_0(B_86)) | ~l1_struct_0(A_87) | ~v7_struct_0(A_87) | v2_struct_0(A_87) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_8, c_249])).
% 2.38/1.31  tff(c_267, plain, (![B_88, A_89]: (v1_xboole_0(u1_struct_0(B_88)) | ~l1_struct_0(A_89) | ~v7_struct_0(A_89) | v2_struct_0(A_89) | u1_struct_0(B_88)=u1_struct_0(A_89) | ~m1_pre_topc(B_88, A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_66, c_262])).
% 2.38/1.31  tff(c_269, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))) | ~l1_struct_0('#skF_1') | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1') | u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_200, c_267])).
% 2.38/1.31  tff(c_272, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))) | v2_struct_0('#skF_1') | u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_242, c_243, c_269])).
% 2.38/1.31  tff(c_273, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_199, c_44, c_272])).
% 2.38/1.31  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.38/1.31  tff(c_276, plain, (~l1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_273, c_6])).
% 2.38/1.31  tff(c_279, plain, (~l1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_164, c_276])).
% 2.38/1.31  tff(c_282, plain, (~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2, c_279])).
% 2.38/1.31  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_282])).
% 2.38/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.31  
% 2.38/1.31  Inference rules
% 2.38/1.31  ----------------------
% 2.38/1.31  #Ref     : 0
% 2.38/1.31  #Sup     : 32
% 2.38/1.31  #Fact    : 0
% 2.38/1.31  #Define  : 0
% 2.38/1.31  #Split   : 3
% 2.38/1.31  #Chain   : 0
% 2.38/1.31  #Close   : 0
% 2.38/1.31  
% 2.38/1.31  Ordering : KBO
% 2.38/1.31  
% 2.38/1.31  Simplification rules
% 2.38/1.31  ----------------------
% 2.38/1.31  #Subsume      : 4
% 2.38/1.31  #Demod        : 30
% 2.38/1.31  #Tautology    : 9
% 2.38/1.31  #SimpNegUnit  : 15
% 2.38/1.31  #BackRed      : 0
% 2.38/1.31  
% 2.38/1.31  #Partial instantiations: 0
% 2.38/1.31  #Strategies tried      : 1
% 2.38/1.31  
% 2.38/1.31  Timing (in seconds)
% 2.38/1.31  ----------------------
% 2.38/1.31  Preprocessing        : 0.32
% 2.38/1.31  Parsing              : 0.18
% 2.38/1.31  CNF conversion       : 0.02
% 2.38/1.31  Main loop            : 0.22
% 2.38/1.31  Inferencing          : 0.09
% 2.38/1.31  Reduction            : 0.06
% 2.38/1.31  Demodulation         : 0.04
% 2.38/1.31  BG Simplification    : 0.01
% 2.38/1.31  Subsumption          : 0.04
% 2.38/1.31  Abstraction          : 0.01
% 2.38/1.31  MUC search           : 0.00
% 2.38/1.31  Cooper               : 0.00
% 2.38/1.31  Total                : 0.58
% 2.38/1.31  Index Insertion      : 0.00
% 2.38/1.31  Index Deletion       : 0.00
% 2.38/1.31  Index Matching       : 0.00
% 2.38/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
