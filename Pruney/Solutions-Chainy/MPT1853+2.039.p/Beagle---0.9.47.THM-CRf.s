%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:05 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 344 expanded)
%              Number of leaves         :   39 ( 127 expanded)
%              Depth                    :   14
%              Number of atoms          :  270 ( 897 expanded)
%              Number of equality atoms :   30 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_153,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ~ ( u1_struct_0(B) = u1_struct_0(A)
              & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_164,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_80,plain,(
    ! [A_53,B_54] :
      ( k6_domain_1(A_53,B_54) = k1_tarski(B_54)
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_84,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_80])).

tff(c_85,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_10,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_85,c_10])).

tff(c_92,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_89])).

tff(c_95,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_95])).

tff(c_101,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_100,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_62,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_77,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_104,plain,(
    v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_77])).

tff(c_115,plain,(
    ! [A_61,B_62] :
      ( ~ v1_zfmisc_1(A_61)
      | ~ v1_subset_1(k6_domain_1(A_61,B_62),A_61)
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_118,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | ~ v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_115])).

tff(c_120,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_104,c_118])).

tff(c_121,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_120])).

tff(c_167,plain,(
    ! [A_73,B_74] :
      ( m1_pre_topc(k1_tex_2(A_73,B_74),A_73)
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_169,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_167])).

tff(c_172,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_169])).

tff(c_173,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_172])).

tff(c_274,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1('#skF_1'(A_85,B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | v1_tex_2(B_86,A_85)
      | ~ m1_pre_topc(B_86,A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ! [B_25,A_24] :
      ( v1_subset_1(B_25,A_24)
      | B_25 = A_24
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_348,plain,(
    ! [A_96,B_97] :
      ( v1_subset_1('#skF_1'(A_96,B_97),u1_struct_0(A_96))
      | u1_struct_0(A_96) = '#skF_1'(A_96,B_97)
      | v1_tex_2(B_97,A_96)
      | ~ m1_pre_topc(B_97,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_274,c_26])).

tff(c_20,plain,(
    ! [A_14,B_20] :
      ( ~ v1_subset_1('#skF_1'(A_14,B_20),u1_struct_0(A_14))
      | v1_tex_2(B_20,A_14)
      | ~ m1_pre_topc(B_20,A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_358,plain,(
    ! [A_98,B_99] :
      ( u1_struct_0(A_98) = '#skF_1'(A_98,B_99)
      | v1_tex_2(B_99,A_98)
      | ~ m1_pre_topc(B_99,A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_348,c_20])).

tff(c_56,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_103,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_56])).

tff(c_364,plain,
    ( '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_358,c_103])).

tff(c_368,plain,(
    '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_173,c_364])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( l1_pre_topc(B_6)
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_176,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_173,c_8])).

tff(c_179,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_176])).

tff(c_122,plain,(
    ! [A_63,B_64] :
      ( v7_struct_0(k1_tex_2(A_63,B_64))
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l1_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_125,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_128,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_125])).

tff(c_129,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_128])).

tff(c_180,plain,(
    ! [B_75,A_76] :
      ( u1_struct_0(B_75) = '#skF_1'(A_76,B_75)
      | v1_tex_2(B_75,A_76)
      | ~ m1_pre_topc(B_75,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_186,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_180,c_103])).

tff(c_190,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_173,c_186])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_zfmisc_1(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | ~ v7_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_211,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_12])).

tff(c_232,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_211])).

tff(c_235,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_238,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_235])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_238])).

tff(c_243,plain,(
    v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_399,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_243])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_399])).

tff(c_403,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_477,plain,(
    ! [B_121,A_122] :
      ( ~ v1_tex_2(B_121,A_122)
      | u1_struct_0(B_121) != u1_struct_0(A_122)
      | ~ m1_pre_topc(B_121,A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_480,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) != u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_403,c_477])).

tff(c_483,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) != u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_480])).

tff(c_484,plain,(
    ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_483])).

tff(c_501,plain,(
    ! [A_127,B_128] :
      ( m1_pre_topc(k1_tex_2(A_127,B_128),A_127)
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l1_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_503,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_501])).

tff(c_506,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_503])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_484,c_506])).

tff(c_510,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_513,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_510,c_8])).

tff(c_516,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_513])).

tff(c_509,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_446,plain,(
    ! [A_113,B_114] :
      ( ~ v2_struct_0(k1_tex_2(A_113,B_114))
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_449,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_446])).

tff(c_452,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_449])).

tff(c_453,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_452])).

tff(c_410,plain,(
    ! [A_107,B_108] :
      ( k6_domain_1(A_107,B_108) = k1_tarski(B_108)
      | ~ m1_subset_1(B_108,A_107)
      | v1_xboole_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_414,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_410])).

tff(c_415,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_423,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_415,c_10])).

tff(c_426,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_423])).

tff(c_429,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_426])).

tff(c_433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_429])).

tff(c_435,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_434,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_407,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_56])).

tff(c_436,plain,(
    ~ v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_407])).

tff(c_462,plain,(
    ! [A_117,B_118] :
      ( v1_subset_1(k6_domain_1(A_117,B_118),A_117)
      | ~ m1_subset_1(B_118,A_117)
      | v1_zfmisc_1(A_117)
      | v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_465,plain,
    ( v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_462])).

tff(c_467,plain,
    ( v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_465])).

tff(c_468,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_436,c_467])).

tff(c_16,plain,(
    ! [B_13,A_11] :
      ( r1_tarski(u1_struct_0(B_13),u1_struct_0(A_11))
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_441,plain,(
    ! [B_111,A_112] :
      ( B_111 = A_112
      | ~ r1_tarski(A_112,B_111)
      | ~ v1_zfmisc_1(B_111)
      | v1_xboole_0(B_111)
      | v1_xboole_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_558,plain,(
    ! [B_143,A_144] :
      ( u1_struct_0(B_143) = u1_struct_0(A_144)
      | ~ v1_zfmisc_1(u1_struct_0(A_144))
      | v1_xboole_0(u1_struct_0(A_144))
      | v1_xboole_0(u1_struct_0(B_143))
      | ~ m1_pre_topc(B_143,A_144)
      | ~ l1_pre_topc(A_144) ) ),
    inference(resolution,[status(thm)],[c_16,c_441])).

tff(c_560,plain,(
    ! [B_143] :
      ( u1_struct_0(B_143) = u1_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0(B_143))
      | ~ m1_pre_topc(B_143,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_468,c_558])).

tff(c_568,plain,(
    ! [B_143] :
      ( u1_struct_0(B_143) = u1_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0(B_143))
      | ~ m1_pre_topc(B_143,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_560])).

tff(c_572,plain,(
    ! [B_145] :
      ( u1_struct_0(B_145) = u1_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0(B_145))
      | ~ m1_pre_topc(B_145,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_568])).

tff(c_582,plain,(
    ! [B_146] :
      ( ~ l1_struct_0(B_146)
      | v2_struct_0(B_146)
      | u1_struct_0(B_146) = u1_struct_0('#skF_2')
      | ~ m1_pre_topc(B_146,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_572,c_10])).

tff(c_585,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_510,c_582])).

tff(c_588,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_453,c_585])).

tff(c_591,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_588])).

tff(c_595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.50  
% 2.94/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.50  %$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.94/1.50  
% 2.94/1.50  %Foreground sorts:
% 2.94/1.50  
% 2.94/1.50  
% 2.94/1.50  %Background operators:
% 2.94/1.50  
% 2.94/1.50  
% 2.94/1.50  %Foreground operators:
% 2.94/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.94/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.50  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.94/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.94/1.50  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.94/1.50  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.94/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.94/1.50  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.94/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.94/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.50  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.94/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.94/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.51  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.94/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.51  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.94/1.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.94/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.94/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.94/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.51  
% 3.22/1.53  tff(f_177, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 3.22/1.53  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.22/1.53  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.22/1.53  tff(f_50, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.22/1.53  tff(f_153, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 3.22/1.53  tff(f_105, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.22/1.53  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 3.22/1.53  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.22/1.53  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.22/1.53  tff(f_119, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.22/1.53  tff(f_56, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.22/1.53  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tex_2)).
% 3.22/1.53  tff(f_164, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 3.22/1.53  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.22/1.53  tff(f_142, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.22/1.53  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.22/1.53  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.22/1.53  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.53  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.22/1.53  tff(c_80, plain, (![A_53, B_54]: (k6_domain_1(A_53, B_54)=k1_tarski(B_54) | ~m1_subset_1(B_54, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.22/1.53  tff(c_84, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_80])).
% 3.22/1.53  tff(c_85, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_84])).
% 3.22/1.53  tff(c_10, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.22/1.53  tff(c_89, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_85, c_10])).
% 3.22/1.53  tff(c_92, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_89])).
% 3.22/1.53  tff(c_95, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_92])).
% 3.22/1.53  tff(c_99, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_95])).
% 3.22/1.53  tff(c_101, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_84])).
% 3.22/1.53  tff(c_100, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_84])).
% 3.22/1.53  tff(c_62, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.22/1.53  tff(c_77, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.22/1.53  tff(c_104, plain, (v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_77])).
% 3.22/1.53  tff(c_115, plain, (![A_61, B_62]: (~v1_zfmisc_1(A_61) | ~v1_subset_1(k6_domain_1(A_61, B_62), A_61) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.22/1.53  tff(c_118, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | ~v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_115])).
% 3.22/1.53  tff(c_120, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_104, c_118])).
% 3.22/1.53  tff(c_121, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_101, c_120])).
% 3.22/1.53  tff(c_167, plain, (![A_73, B_74]: (m1_pre_topc(k1_tex_2(A_73, B_74), A_73) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.22/1.53  tff(c_169, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_167])).
% 3.22/1.53  tff(c_172, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_169])).
% 3.22/1.53  tff(c_173, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_172])).
% 3.22/1.53  tff(c_274, plain, (![A_85, B_86]: (m1_subset_1('#skF_1'(A_85, B_86), k1_zfmisc_1(u1_struct_0(A_85))) | v1_tex_2(B_86, A_85) | ~m1_pre_topc(B_86, A_85) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.53  tff(c_26, plain, (![B_25, A_24]: (v1_subset_1(B_25, A_24) | B_25=A_24 | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.22/1.53  tff(c_348, plain, (![A_96, B_97]: (v1_subset_1('#skF_1'(A_96, B_97), u1_struct_0(A_96)) | u1_struct_0(A_96)='#skF_1'(A_96, B_97) | v1_tex_2(B_97, A_96) | ~m1_pre_topc(B_97, A_96) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_274, c_26])).
% 3.22/1.53  tff(c_20, plain, (![A_14, B_20]: (~v1_subset_1('#skF_1'(A_14, B_20), u1_struct_0(A_14)) | v1_tex_2(B_20, A_14) | ~m1_pre_topc(B_20, A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.53  tff(c_358, plain, (![A_98, B_99]: (u1_struct_0(A_98)='#skF_1'(A_98, B_99) | v1_tex_2(B_99, A_98) | ~m1_pre_topc(B_99, A_98) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_348, c_20])).
% 3.22/1.53  tff(c_56, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.22/1.53  tff(c_103, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_56])).
% 3.22/1.53  tff(c_364, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_358, c_103])).
% 3.22/1.53  tff(c_368, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_173, c_364])).
% 3.22/1.53  tff(c_8, plain, (![B_6, A_4]: (l1_pre_topc(B_6) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.22/1.53  tff(c_176, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_173, c_8])).
% 3.22/1.53  tff(c_179, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_176])).
% 3.22/1.53  tff(c_122, plain, (![A_63, B_64]: (v7_struct_0(k1_tex_2(A_63, B_64)) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l1_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.22/1.53  tff(c_125, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_122])).
% 3.22/1.53  tff(c_128, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_125])).
% 3.22/1.53  tff(c_129, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_128])).
% 3.22/1.53  tff(c_180, plain, (![B_75, A_76]: (u1_struct_0(B_75)='#skF_1'(A_76, B_75) | v1_tex_2(B_75, A_76) | ~m1_pre_topc(B_75, A_76) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.53  tff(c_186, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_180, c_103])).
% 3.22/1.53  tff(c_190, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_173, c_186])).
% 3.22/1.53  tff(c_12, plain, (![A_8]: (v1_zfmisc_1(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | ~v7_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.53  tff(c_211, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_12])).
% 3.22/1.53  tff(c_232, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_211])).
% 3.22/1.53  tff(c_235, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_232])).
% 3.22/1.53  tff(c_238, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_235])).
% 3.22/1.53  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_238])).
% 3.22/1.53  tff(c_243, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_232])).
% 3.22/1.53  tff(c_399, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_243])).
% 3.22/1.53  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_399])).
% 3.22/1.53  tff(c_403, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 3.22/1.53  tff(c_477, plain, (![B_121, A_122]: (~v1_tex_2(B_121, A_122) | u1_struct_0(B_121)!=u1_struct_0(A_122) | ~m1_pre_topc(B_121, A_122) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.22/1.53  tff(c_480, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_403, c_477])).
% 3.22/1.53  tff(c_483, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_480])).
% 3.22/1.53  tff(c_484, plain, (~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_483])).
% 3.22/1.53  tff(c_501, plain, (![A_127, B_128]: (m1_pre_topc(k1_tex_2(A_127, B_128), A_127) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l1_pre_topc(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.22/1.53  tff(c_503, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_501])).
% 3.22/1.53  tff(c_506, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_503])).
% 3.22/1.53  tff(c_508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_484, c_506])).
% 3.22/1.53  tff(c_510, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_483])).
% 3.22/1.53  tff(c_513, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_510, c_8])).
% 3.22/1.53  tff(c_516, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_513])).
% 3.22/1.53  tff(c_509, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_483])).
% 3.22/1.53  tff(c_446, plain, (![A_113, B_114]: (~v2_struct_0(k1_tex_2(A_113, B_114)) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.22/1.53  tff(c_449, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_446])).
% 3.22/1.53  tff(c_452, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_449])).
% 3.22/1.53  tff(c_453, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_452])).
% 3.22/1.53  tff(c_410, plain, (![A_107, B_108]: (k6_domain_1(A_107, B_108)=k1_tarski(B_108) | ~m1_subset_1(B_108, A_107) | v1_xboole_0(A_107))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.22/1.53  tff(c_414, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_410])).
% 3.22/1.53  tff(c_415, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_414])).
% 3.22/1.53  tff(c_423, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_415, c_10])).
% 3.22/1.53  tff(c_426, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_423])).
% 3.22/1.53  tff(c_429, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_426])).
% 3.22/1.53  tff(c_433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_429])).
% 3.22/1.53  tff(c_435, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_414])).
% 3.22/1.53  tff(c_434, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_414])).
% 3.22/1.53  tff(c_407, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_403, c_56])).
% 3.22/1.53  tff(c_436, plain, (~v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_407])).
% 3.22/1.53  tff(c_462, plain, (![A_117, B_118]: (v1_subset_1(k6_domain_1(A_117, B_118), A_117) | ~m1_subset_1(B_118, A_117) | v1_zfmisc_1(A_117) | v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.22/1.53  tff(c_465, plain, (v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_434, c_462])).
% 3.22/1.53  tff(c_467, plain, (v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_465])).
% 3.22/1.53  tff(c_468, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_435, c_436, c_467])).
% 3.22/1.53  tff(c_16, plain, (![B_13, A_11]: (r1_tarski(u1_struct_0(B_13), u1_struct_0(A_11)) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.22/1.53  tff(c_441, plain, (![B_111, A_112]: (B_111=A_112 | ~r1_tarski(A_112, B_111) | ~v1_zfmisc_1(B_111) | v1_xboole_0(B_111) | v1_xboole_0(A_112))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.22/1.53  tff(c_558, plain, (![B_143, A_144]: (u1_struct_0(B_143)=u1_struct_0(A_144) | ~v1_zfmisc_1(u1_struct_0(A_144)) | v1_xboole_0(u1_struct_0(A_144)) | v1_xboole_0(u1_struct_0(B_143)) | ~m1_pre_topc(B_143, A_144) | ~l1_pre_topc(A_144))), inference(resolution, [status(thm)], [c_16, c_441])).
% 3.22/1.53  tff(c_560, plain, (![B_143]: (u1_struct_0(B_143)=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0(B_143)) | ~m1_pre_topc(B_143, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_468, c_558])).
% 3.22/1.53  tff(c_568, plain, (![B_143]: (u1_struct_0(B_143)=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0(B_143)) | ~m1_pre_topc(B_143, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_560])).
% 3.22/1.53  tff(c_572, plain, (![B_145]: (u1_struct_0(B_145)=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(B_145)) | ~m1_pre_topc(B_145, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_435, c_568])).
% 3.22/1.53  tff(c_582, plain, (![B_146]: (~l1_struct_0(B_146) | v2_struct_0(B_146) | u1_struct_0(B_146)=u1_struct_0('#skF_2') | ~m1_pre_topc(B_146, '#skF_2'))), inference(resolution, [status(thm)], [c_572, c_10])).
% 3.22/1.53  tff(c_585, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_510, c_582])).
% 3.22/1.53  tff(c_588, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_509, c_453, c_585])).
% 3.22/1.53  tff(c_591, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_588])).
% 3.22/1.53  tff(c_595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_516, c_591])).
% 3.22/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.53  
% 3.22/1.53  Inference rules
% 3.22/1.53  ----------------------
% 3.22/1.53  #Ref     : 0
% 3.22/1.53  #Sup     : 89
% 3.22/1.53  #Fact    : 0
% 3.22/1.53  #Define  : 0
% 3.22/1.53  #Split   : 7
% 3.22/1.53  #Chain   : 0
% 3.22/1.53  #Close   : 0
% 3.22/1.53  
% 3.22/1.53  Ordering : KBO
% 3.22/1.53  
% 3.22/1.53  Simplification rules
% 3.22/1.53  ----------------------
% 3.22/1.53  #Subsume      : 11
% 3.22/1.53  #Demod        : 77
% 3.22/1.53  #Tautology    : 21
% 3.22/1.53  #SimpNegUnit  : 27
% 3.22/1.53  #BackRed      : 14
% 3.22/1.53  
% 3.22/1.53  #Partial instantiations: 0
% 3.22/1.53  #Strategies tried      : 1
% 3.22/1.53  
% 3.22/1.53  Timing (in seconds)
% 3.22/1.53  ----------------------
% 3.22/1.53  Preprocessing        : 0.36
% 3.22/1.53  Parsing              : 0.19
% 3.22/1.53  CNF conversion       : 0.02
% 3.22/1.53  Main loop            : 0.34
% 3.22/1.53  Inferencing          : 0.12
% 3.22/1.53  Reduction            : 0.10
% 3.22/1.53  Demodulation         : 0.06
% 3.22/1.53  BG Simplification    : 0.02
% 3.22/1.53  Subsumption          : 0.06
% 3.22/1.53  Abstraction          : 0.02
% 3.22/1.53  MUC search           : 0.00
% 3.22/1.53  Cooper               : 0.00
% 3.22/1.53  Total                : 0.74
% 3.22/1.53  Index Insertion      : 0.00
% 3.22/1.53  Index Deletion       : 0.00
% 3.22/1.53  Index Matching       : 0.00
% 3.22/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
