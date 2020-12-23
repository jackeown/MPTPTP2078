%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:05 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 469 expanded)
%              Number of leaves         :   38 ( 169 expanded)
%              Depth                    :   14
%              Number of atoms          :  283 (1304 expanded)
%              Number of equality atoms :   31 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_166,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ~ ( u1_struct_0(B) = u1_struct_0(A)
              & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_153,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_53,B_54] :
      ( k6_domain_1(A_53,B_54) = k1_tarski(B_54)
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_88,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_84])).

tff(c_89,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_12,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_93,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_12])).

tff(c_96,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_93])).

tff(c_99,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_99])).

tff(c_104,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_56,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_81,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_110,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_62])).

tff(c_111,plain,(
    v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_110])).

tff(c_165,plain,(
    ! [A_73,B_74] :
      ( m1_pre_topc(k1_tex_2(A_73,B_74),A_73)
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_167,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_165])).

tff(c_170,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_167])).

tff(c_171,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_170])).

tff(c_247,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1('#skF_1'(A_81,B_82),k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_tex_2(B_82,A_81)
      | ~ m1_pre_topc(B_82,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ! [B_25,A_24] :
      ( v1_subset_1(B_25,A_24)
      | B_25 = A_24
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_440,plain,(
    ! [A_105,B_106] :
      ( v1_subset_1('#skF_1'(A_105,B_106),u1_struct_0(A_105))
      | u1_struct_0(A_105) = '#skF_1'(A_105,B_106)
      | v1_tex_2(B_106,A_105)
      | ~ m1_pre_topc(B_106,A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_247,c_26])).

tff(c_20,plain,(
    ! [A_14,B_20] :
      ( ~ v1_subset_1('#skF_1'(A_14,B_20),u1_struct_0(A_14))
      | v1_tex_2(B_20,A_14)
      | ~ m1_pre_topc(B_20,A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_450,plain,(
    ! [A_107,B_108] :
      ( u1_struct_0(A_107) = '#skF_1'(A_107,B_108)
      | v1_tex_2(B_108,A_107)
      | ~ m1_pre_topc(B_108,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_440,c_20])).

tff(c_456,plain,
    ( '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_450,c_81])).

tff(c_460,plain,(
    '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_171,c_456])).

tff(c_146,plain,(
    ! [A_69,B_70] :
      ( ~ v2_struct_0(k1_tex_2(A_69,B_70))
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ l1_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_149,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_146])).

tff(c_152,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_149])).

tff(c_153,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_152])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( l1_pre_topc(B_6)
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_174,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_171,c_8])).

tff(c_177,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_174])).

tff(c_154,plain,(
    ! [B_71,A_72] :
      ( u1_struct_0(B_71) = '#skF_1'(A_72,B_71)
      | v1_tex_2(B_71,A_72)
      | ~ m1_pre_topc(B_71,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_160,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_154,c_81])).

tff(c_164,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_160])).

tff(c_187,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_164])).

tff(c_211,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_12])).

tff(c_233,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_211])).

tff(c_235,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_238,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_235])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_238])).

tff(c_244,plain,(
    l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_122,plain,(
    ! [A_61,B_62] :
      ( v7_struct_0(k1_tex_2(A_61,B_62))
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
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

tff(c_299,plain,(
    ! [A_88,B_89] :
      ( ~ v7_struct_0(A_88)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_88),B_89),u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_struct_0(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_305,plain,(
    ! [B_89] :
      ( ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),B_89),'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1(B_89,u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
      | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_299])).

tff(c_317,plain,(
    ! [B_89] :
      ( ~ v1_subset_1(k6_domain_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')),B_89),'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1(B_89,'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_187,c_187,c_129,c_305])).

tff(c_318,plain,(
    ! [B_89] :
      ( ~ v1_subset_1(k6_domain_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')),B_89),'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1(B_89,'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_317])).

tff(c_661,plain,(
    ! [B_117] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),B_117),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_460,c_460,c_318])).

tff(c_668,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_661])).

tff(c_674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_111,c_668])).

tff(c_676,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_722,plain,(
    ! [B_129,A_130] :
      ( ~ v1_tex_2(B_129,A_130)
      | u1_struct_0(B_129) != u1_struct_0(A_130)
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_725,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) != u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_676,c_722])).

tff(c_728,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) != u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_725])).

tff(c_729,plain,(
    ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_728])).

tff(c_766,plain,(
    ! [A_141,B_142] :
      ( m1_pre_topc(k1_tex_2(A_141,B_142),A_141)
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | ~ l1_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_768,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_766])).

tff(c_771,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_768])).

tff(c_773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_729,c_771])).

tff(c_775,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_778,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_775,c_8])).

tff(c_781,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_778])).

tff(c_774,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_805,plain,(
    ! [A_149,B_150] :
      ( ~ v2_struct_0(k1_tex_2(A_149,B_150))
      | ~ m1_subset_1(B_150,u1_struct_0(A_149))
      | ~ l1_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_808,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_805])).

tff(c_811,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_808])).

tff(c_812,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_811])).

tff(c_682,plain,(
    ! [A_123,B_124] :
      ( k6_domain_1(A_123,B_124) = k1_tarski(B_124)
      | ~ m1_subset_1(B_124,A_123)
      | v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_686,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_682])).

tff(c_687,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_686])).

tff(c_690,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_687,c_12])).

tff(c_693,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_690])).

tff(c_701,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_693])).

tff(c_705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_701])).

tff(c_707,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_686])).

tff(c_706,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_686])).

tff(c_675,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_712,plain,(
    ~ v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_675])).

tff(c_798,plain,(
    ! [A_147,B_148] :
      ( v1_subset_1(k6_domain_1(A_147,B_148),A_147)
      | ~ m1_subset_1(B_148,A_147)
      | v1_zfmisc_1(A_147)
      | v1_xboole_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_801,plain,
    ( v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_798])).

tff(c_803,plain,
    ( v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_801])).

tff(c_804,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_712,c_803])).

tff(c_16,plain,(
    ! [B_13,A_11] :
      ( r1_tarski(u1_struct_0(B_13),u1_struct_0(A_11))
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_717,plain,(
    ! [B_127,A_128] :
      ( B_127 = A_128
      | ~ r1_tarski(A_128,B_127)
      | ~ v1_zfmisc_1(B_127)
      | v1_xboole_0(B_127)
      | v1_xboole_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_861,plain,(
    ! [B_165,A_166] :
      ( u1_struct_0(B_165) = u1_struct_0(A_166)
      | ~ v1_zfmisc_1(u1_struct_0(A_166))
      | v1_xboole_0(u1_struct_0(A_166))
      | v1_xboole_0(u1_struct_0(B_165))
      | ~ m1_pre_topc(B_165,A_166)
      | ~ l1_pre_topc(A_166) ) ),
    inference(resolution,[status(thm)],[c_16,c_717])).

tff(c_863,plain,(
    ! [B_165] :
      ( u1_struct_0(B_165) = u1_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0(B_165))
      | ~ m1_pre_topc(B_165,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_804,c_861])).

tff(c_869,plain,(
    ! [B_165] :
      ( u1_struct_0(B_165) = u1_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0(B_165))
      | ~ m1_pre_topc(B_165,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_863])).

tff(c_872,plain,(
    ! [B_167] :
      ( u1_struct_0(B_167) = u1_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0(B_167))
      | ~ m1_pre_topc(B_167,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_869])).

tff(c_882,plain,(
    ! [B_168] :
      ( ~ l1_struct_0(B_168)
      | v2_struct_0(B_168)
      | u1_struct_0(B_168) = u1_struct_0('#skF_2')
      | ~ m1_pre_topc(B_168,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_872,c_12])).

tff(c_885,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_775,c_882])).

tff(c_888,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_774,c_812,c_885])).

tff(c_892,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_888])).

tff(c_896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_892])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:24:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.50  
% 3.27/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.50  %$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.27/1.50  
% 3.27/1.50  %Foreground sorts:
% 3.27/1.50  
% 3.27/1.50  
% 3.27/1.50  %Background operators:
% 3.27/1.50  
% 3.27/1.50  
% 3.27/1.50  %Foreground operators:
% 3.27/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.50  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.27/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.50  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.27/1.50  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.27/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.27/1.50  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.27/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.50  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.27/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.50  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.50  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.27/1.50  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.27/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.27/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.27/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.27/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.50  
% 3.27/1.52  tff(f_179, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 3.27/1.52  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.27/1.52  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.27/1.52  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.27/1.52  tff(f_105, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.27/1.52  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 3.27/1.52  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.27/1.52  tff(f_119, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.27/1.52  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.27/1.52  tff(f_166, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 3.27/1.52  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 3.27/1.52  tff(f_153, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 3.27/1.52  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.27/1.52  tff(f_142, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 3.27/1.52  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.27/1.52  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.27/1.52  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.27/1.52  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.52  tff(c_84, plain, (![A_53, B_54]: (k6_domain_1(A_53, B_54)=k1_tarski(B_54) | ~m1_subset_1(B_54, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.27/1.52  tff(c_88, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_84])).
% 3.27/1.52  tff(c_89, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_88])).
% 3.27/1.52  tff(c_12, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.27/1.52  tff(c_93, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_89, c_12])).
% 3.27/1.52  tff(c_96, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_93])).
% 3.27/1.52  tff(c_99, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_96])).
% 3.27/1.52  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_99])).
% 3.27/1.52  tff(c_104, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_88])).
% 3.27/1.52  tff(c_56, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.27/1.52  tff(c_81, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 3.27/1.52  tff(c_62, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.27/1.52  tff(c_110, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_81, c_62])).
% 3.27/1.52  tff(c_111, plain, (v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_110])).
% 3.27/1.52  tff(c_165, plain, (![A_73, B_74]: (m1_pre_topc(k1_tex_2(A_73, B_74), A_73) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.27/1.52  tff(c_167, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_165])).
% 3.27/1.52  tff(c_170, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_167])).
% 3.27/1.52  tff(c_171, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_170])).
% 3.27/1.52  tff(c_247, plain, (![A_81, B_82]: (m1_subset_1('#skF_1'(A_81, B_82), k1_zfmisc_1(u1_struct_0(A_81))) | v1_tex_2(B_82, A_81) | ~m1_pre_topc(B_82, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.27/1.52  tff(c_26, plain, (![B_25, A_24]: (v1_subset_1(B_25, A_24) | B_25=A_24 | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.27/1.52  tff(c_440, plain, (![A_105, B_106]: (v1_subset_1('#skF_1'(A_105, B_106), u1_struct_0(A_105)) | u1_struct_0(A_105)='#skF_1'(A_105, B_106) | v1_tex_2(B_106, A_105) | ~m1_pre_topc(B_106, A_105) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_247, c_26])).
% 3.27/1.52  tff(c_20, plain, (![A_14, B_20]: (~v1_subset_1('#skF_1'(A_14, B_20), u1_struct_0(A_14)) | v1_tex_2(B_20, A_14) | ~m1_pre_topc(B_20, A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.27/1.52  tff(c_450, plain, (![A_107, B_108]: (u1_struct_0(A_107)='#skF_1'(A_107, B_108) | v1_tex_2(B_108, A_107) | ~m1_pre_topc(B_108, A_107) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_440, c_20])).
% 3.27/1.52  tff(c_456, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_450, c_81])).
% 3.27/1.52  tff(c_460, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_171, c_456])).
% 3.27/1.52  tff(c_146, plain, (![A_69, B_70]: (~v2_struct_0(k1_tex_2(A_69, B_70)) | ~m1_subset_1(B_70, u1_struct_0(A_69)) | ~l1_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.27/1.52  tff(c_149, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_146])).
% 3.27/1.52  tff(c_152, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_149])).
% 3.27/1.52  tff(c_153, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_152])).
% 3.27/1.52  tff(c_8, plain, (![B_6, A_4]: (l1_pre_topc(B_6) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.27/1.52  tff(c_174, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_171, c_8])).
% 3.27/1.52  tff(c_177, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_174])).
% 3.27/1.52  tff(c_154, plain, (![B_71, A_72]: (u1_struct_0(B_71)='#skF_1'(A_72, B_71) | v1_tex_2(B_71, A_72) | ~m1_pre_topc(B_71, A_72) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.27/1.52  tff(c_160, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_154, c_81])).
% 3.27/1.52  tff(c_164, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_160])).
% 3.27/1.52  tff(c_187, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_164])).
% 3.27/1.52  tff(c_211, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_12])).
% 3.27/1.52  tff(c_233, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_153, c_211])).
% 3.27/1.52  tff(c_235, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_233])).
% 3.27/1.52  tff(c_238, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_235])).
% 3.27/1.52  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_238])).
% 3.27/1.52  tff(c_244, plain, (l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_233])).
% 3.27/1.52  tff(c_122, plain, (![A_61, B_62]: (v7_struct_0(k1_tex_2(A_61, B_62)) | ~m1_subset_1(B_62, u1_struct_0(A_61)) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.27/1.52  tff(c_125, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_122])).
% 3.27/1.52  tff(c_128, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_125])).
% 3.27/1.52  tff(c_129, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_128])).
% 3.27/1.52  tff(c_299, plain, (![A_88, B_89]: (~v7_struct_0(A_88) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_88), B_89), u1_struct_0(A_88)) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_struct_0(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.27/1.52  tff(c_305, plain, (![B_89]: (~v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), B_89), '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1(B_89, u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_187, c_299])).
% 3.27/1.52  tff(c_317, plain, (![B_89]: (~v1_subset_1(k6_domain_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')), B_89), '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1(B_89, '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_187, c_187, c_129, c_305])).
% 3.27/1.52  tff(c_318, plain, (![B_89]: (~v1_subset_1(k6_domain_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')), B_89), '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1(B_89, '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_153, c_317])).
% 3.27/1.52  tff(c_661, plain, (![B_117]: (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), B_117), u1_struct_0('#skF_2')) | ~m1_subset_1(B_117, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_460, c_460, c_318])).
% 3.27/1.52  tff(c_668, plain, (~v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_661])).
% 3.27/1.52  tff(c_674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_111, c_668])).
% 3.27/1.52  tff(c_676, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 3.27/1.52  tff(c_722, plain, (![B_129, A_130]: (~v1_tex_2(B_129, A_130) | u1_struct_0(B_129)!=u1_struct_0(A_130) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.27/1.52  tff(c_725, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_676, c_722])).
% 3.27/1.52  tff(c_728, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_725])).
% 3.27/1.52  tff(c_729, plain, (~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_728])).
% 3.27/1.52  tff(c_766, plain, (![A_141, B_142]: (m1_pre_topc(k1_tex_2(A_141, B_142), A_141) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | ~l1_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.27/1.52  tff(c_768, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_766])).
% 3.27/1.52  tff(c_771, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_768])).
% 3.27/1.52  tff(c_773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_729, c_771])).
% 3.27/1.52  tff(c_775, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_728])).
% 3.27/1.52  tff(c_778, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_775, c_8])).
% 3.27/1.52  tff(c_781, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_778])).
% 3.27/1.52  tff(c_774, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_728])).
% 3.27/1.52  tff(c_805, plain, (![A_149, B_150]: (~v2_struct_0(k1_tex_2(A_149, B_150)) | ~m1_subset_1(B_150, u1_struct_0(A_149)) | ~l1_pre_topc(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.27/1.52  tff(c_808, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_805])).
% 3.27/1.52  tff(c_811, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_808])).
% 3.27/1.52  tff(c_812, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_811])).
% 3.27/1.52  tff(c_682, plain, (![A_123, B_124]: (k6_domain_1(A_123, B_124)=k1_tarski(B_124) | ~m1_subset_1(B_124, A_123) | v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.27/1.52  tff(c_686, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_682])).
% 3.27/1.52  tff(c_687, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_686])).
% 3.27/1.52  tff(c_690, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_687, c_12])).
% 3.27/1.52  tff(c_693, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_690])).
% 3.27/1.52  tff(c_701, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_693])).
% 3.27/1.52  tff(c_705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_701])).
% 3.27/1.52  tff(c_707, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_686])).
% 3.27/1.52  tff(c_706, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_686])).
% 3.27/1.52  tff(c_675, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 3.27/1.52  tff(c_712, plain, (~v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_706, c_675])).
% 3.27/1.52  tff(c_798, plain, (![A_147, B_148]: (v1_subset_1(k6_domain_1(A_147, B_148), A_147) | ~m1_subset_1(B_148, A_147) | v1_zfmisc_1(A_147) | v1_xboole_0(A_147))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.27/1.52  tff(c_801, plain, (v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_706, c_798])).
% 3.27/1.52  tff(c_803, plain, (v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_801])).
% 3.27/1.52  tff(c_804, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_707, c_712, c_803])).
% 3.27/1.52  tff(c_16, plain, (![B_13, A_11]: (r1_tarski(u1_struct_0(B_13), u1_struct_0(A_11)) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.27/1.52  tff(c_717, plain, (![B_127, A_128]: (B_127=A_128 | ~r1_tarski(A_128, B_127) | ~v1_zfmisc_1(B_127) | v1_xboole_0(B_127) | v1_xboole_0(A_128))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.27/1.52  tff(c_861, plain, (![B_165, A_166]: (u1_struct_0(B_165)=u1_struct_0(A_166) | ~v1_zfmisc_1(u1_struct_0(A_166)) | v1_xboole_0(u1_struct_0(A_166)) | v1_xboole_0(u1_struct_0(B_165)) | ~m1_pre_topc(B_165, A_166) | ~l1_pre_topc(A_166))), inference(resolution, [status(thm)], [c_16, c_717])).
% 3.27/1.52  tff(c_863, plain, (![B_165]: (u1_struct_0(B_165)=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0(B_165)) | ~m1_pre_topc(B_165, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_804, c_861])).
% 3.27/1.52  tff(c_869, plain, (![B_165]: (u1_struct_0(B_165)=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0(B_165)) | ~m1_pre_topc(B_165, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_863])).
% 3.27/1.52  tff(c_872, plain, (![B_167]: (u1_struct_0(B_167)=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(B_167)) | ~m1_pre_topc(B_167, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_707, c_869])).
% 3.27/1.52  tff(c_882, plain, (![B_168]: (~l1_struct_0(B_168) | v2_struct_0(B_168) | u1_struct_0(B_168)=u1_struct_0('#skF_2') | ~m1_pre_topc(B_168, '#skF_2'))), inference(resolution, [status(thm)], [c_872, c_12])).
% 3.27/1.52  tff(c_885, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_775, c_882])).
% 3.27/1.52  tff(c_888, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_774, c_812, c_885])).
% 3.27/1.52  tff(c_892, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_888])).
% 3.27/1.52  tff(c_896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_781, c_892])).
% 3.27/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.52  
% 3.27/1.52  Inference rules
% 3.27/1.52  ----------------------
% 3.27/1.52  #Ref     : 0
% 3.27/1.52  #Sup     : 140
% 3.27/1.52  #Fact    : 0
% 3.27/1.52  #Define  : 0
% 3.27/1.52  #Split   : 10
% 3.27/1.52  #Chain   : 0
% 3.27/1.52  #Close   : 0
% 3.27/1.52  
% 3.27/1.52  Ordering : KBO
% 3.27/1.52  
% 3.27/1.52  Simplification rules
% 3.27/1.52  ----------------------
% 3.27/1.52  #Subsume      : 26
% 3.27/1.52  #Demod        : 154
% 3.27/1.52  #Tautology    : 33
% 3.27/1.52  #SimpNegUnit  : 60
% 3.27/1.52  #BackRed      : 20
% 3.27/1.52  
% 3.27/1.52  #Partial instantiations: 0
% 3.27/1.52  #Strategies tried      : 1
% 3.27/1.52  
% 3.27/1.52  Timing (in seconds)
% 3.27/1.52  ----------------------
% 3.27/1.52  Preprocessing        : 0.34
% 3.27/1.52  Parsing              : 0.18
% 3.27/1.52  CNF conversion       : 0.02
% 3.27/1.52  Main loop            : 0.39
% 3.27/1.52  Inferencing          : 0.14
% 3.27/1.52  Reduction            : 0.12
% 3.27/1.52  Demodulation         : 0.08
% 3.27/1.53  BG Simplification    : 0.02
% 3.27/1.53  Subsumption          : 0.07
% 3.27/1.53  Abstraction          : 0.02
% 3.27/1.53  MUC search           : 0.00
% 3.27/1.53  Cooper               : 0.00
% 3.27/1.53  Total                : 0.78
% 3.27/1.53  Index Insertion      : 0.00
% 3.27/1.53  Index Deletion       : 0.00
% 3.27/1.53  Index Matching       : 0.00
% 3.27/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
