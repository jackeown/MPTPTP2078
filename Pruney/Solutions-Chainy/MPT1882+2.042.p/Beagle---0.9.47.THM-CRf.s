%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:18 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 365 expanded)
%              Number of leaves         :   29 ( 134 expanded)
%              Depth                    :   13
%              Number of atoms          :  222 (1372 expanded)
%              Number of equality atoms :   10 (  67 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_52,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_70,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_83,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_46,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_53,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_54,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_52])).

tff(c_14,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_1'(A_8),A_8)
      | ~ v1_zfmisc_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_172,plain,(
    ! [A_59,B_60] :
      ( '#skF_2'(A_59,B_60) != B_60
      | v3_tex_2(B_60,A_59)
      | ~ v2_tex_2(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_183,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_172])).

tff(c_188,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_183])).

tff(c_189,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_188])).

tff(c_190,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_40,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_254,plain,(
    ! [B_75,A_76] :
      ( v2_tex_2(B_75,A_76)
      | ~ v1_zfmisc_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | v1_xboole_0(B_75)
      | ~ l1_pre_topc(A_76)
      | ~ v2_tdlat_3(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_265,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_254])).

tff(c_270,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_54,c_265])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_190,c_270])).

tff(c_274,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_275,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(B_77,'#skF_2'(A_78,B_77))
      | v3_tex_2(B_77,A_78)
      | ~ v2_tex_2(B_77,A_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_283,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_275])).

tff(c_288,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_274,c_283])).

tff(c_289,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_288])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    ! [C_37,B_38,A_39] :
      ( ~ v1_xboole_0(C_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_93,plain,(
    ! [B_40,A_41,A_42] :
      ( ~ v1_xboole_0(B_40)
      | ~ r2_hidden(A_41,A_42)
      | ~ r1_tarski(A_42,B_40) ) ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_96,plain,(
    ! [B_40,B_2,A_1] :
      ( ~ v1_xboole_0(B_40)
      | ~ r1_tarski(B_2,B_40)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_2,c_93])).

tff(c_294,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_1,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_289,c_96])).

tff(c_300,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
      | ~ m1_subset_1(A_1,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_294])).

tff(c_301,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_273,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_28,plain,(
    ! [B_24,A_22] :
      ( B_24 = A_22
      | ~ r1_tarski(A_22,B_24)
      | ~ v1_zfmisc_1(B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_292,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_289,c_28])).

tff(c_297,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_273,c_292])).

tff(c_302,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_333,plain,(
    ! [A_85,B_86] :
      ( v2_tex_2('#skF_2'(A_85,B_86),A_85)
      | v3_tex_2(B_86,A_85)
      | ~ v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_341,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_333])).

tff(c_346,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_274,c_341])).

tff(c_347,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_346])).

tff(c_22,plain,(
    ! [A_12,B_18] :
      ( m1_subset_1('#skF_2'(A_12,B_18),k1_zfmisc_1(u1_struct_0(A_12)))
      | v3_tex_2(B_18,A_12)
      | ~ v2_tex_2(B_18,A_12)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_435,plain,(
    ! [B_99,A_100] :
      ( v1_zfmisc_1(B_99)
      | ~ v2_tex_2(B_99,A_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | v1_xboole_0(B_99)
      | ~ l1_pre_topc(A_100)
      | ~ v2_tdlat_3(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_626,plain,(
    ! [A_135,B_136] :
      ( v1_zfmisc_1('#skF_2'(A_135,B_136))
      | ~ v2_tex_2('#skF_2'(A_135,B_136),A_135)
      | v1_xboole_0('#skF_2'(A_135,B_136))
      | ~ v2_tdlat_3(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135)
      | v3_tex_2(B_136,A_135)
      | ~ v2_tex_2(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_22,c_435])).

tff(c_634,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_347,c_626])).

tff(c_640,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_274,c_42,c_40,c_634])).

tff(c_642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_44,c_301,c_302,c_640])).

tff(c_643,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_301])).

tff(c_649,plain,(
    ! [A_137] : ~ m1_subset_1(A_137,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_653,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_649])).

tff(c_656,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_653])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_656])).

tff(c_659,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_660,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_732,plain,(
    ! [B_159,A_160] :
      ( v2_tex_2(B_159,A_160)
      | ~ v3_tex_2(B_159,A_160)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_743,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_732])).

tff(c_748,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_660,c_743])).

tff(c_887,plain,(
    ! [B_188,A_189] :
      ( v1_zfmisc_1(B_188)
      | ~ v2_tex_2(B_188,A_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_189)))
      | v1_xboole_0(B_188)
      | ~ l1_pre_topc(A_189)
      | ~ v2_tdlat_3(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_898,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_887])).

tff(c_903,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_748,c_898])).

tff(c_905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_659,c_903])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.52  
% 3.13/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.52  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.13/1.52  
% 3.13/1.52  %Foreground sorts:
% 3.13/1.52  
% 3.13/1.52  
% 3.13/1.52  %Background operators:
% 3.13/1.52  
% 3.13/1.52  
% 3.13/1.52  %Foreground operators:
% 3.13/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.13/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.13/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.13/1.52  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.13/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.52  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.13/1.52  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.13/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.52  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.13/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.13/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.13/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.52  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.13/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.52  
% 3.27/1.53  tff(f_122, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 3.27/1.53  tff(f_52, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 3.27/1.53  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.27/1.53  tff(f_102, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.27/1.53  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.27/1.53  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.27/1.53  tff(f_42, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.27/1.53  tff(f_83, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.27/1.53  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.27/1.53  tff(c_36, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.27/1.53  tff(c_46, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.27/1.53  tff(c_53, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 3.27/1.53  tff(c_52, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.27/1.53  tff(c_54, plain, (v1_zfmisc_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_53, c_52])).
% 3.27/1.53  tff(c_14, plain, (![A_8]: (m1_subset_1('#skF_1'(A_8), A_8) | ~v1_zfmisc_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.27/1.53  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.27/1.53  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.27/1.53  tff(c_172, plain, (![A_59, B_60]: ('#skF_2'(A_59, B_60)!=B_60 | v3_tex_2(B_60, A_59) | ~v2_tex_2(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.27/1.53  tff(c_183, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_172])).
% 3.27/1.53  tff(c_188, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_183])).
% 3.27/1.53  tff(c_189, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_53, c_188])).
% 3.27/1.53  tff(c_190, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_189])).
% 3.27/1.53  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.27/1.53  tff(c_40, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.27/1.53  tff(c_254, plain, (![B_75, A_76]: (v2_tex_2(B_75, A_76) | ~v1_zfmisc_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | v1_xboole_0(B_75) | ~l1_pre_topc(A_76) | ~v2_tdlat_3(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.27/1.53  tff(c_265, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_254])).
% 3.27/1.53  tff(c_270, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_54, c_265])).
% 3.27/1.53  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_190, c_270])).
% 3.27/1.53  tff(c_274, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_189])).
% 3.27/1.53  tff(c_275, plain, (![B_77, A_78]: (r1_tarski(B_77, '#skF_2'(A_78, B_77)) | v3_tex_2(B_77, A_78) | ~v2_tex_2(B_77, A_78) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.27/1.53  tff(c_283, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_275])).
% 3.27/1.53  tff(c_288, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_274, c_283])).
% 3.27/1.53  tff(c_289, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_53, c_288])).
% 3.27/1.53  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.53  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.53  tff(c_81, plain, (![C_37, B_38, A_39]: (~v1_xboole_0(C_37) | ~m1_subset_1(B_38, k1_zfmisc_1(C_37)) | ~r2_hidden(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.27/1.53  tff(c_93, plain, (![B_40, A_41, A_42]: (~v1_xboole_0(B_40) | ~r2_hidden(A_41, A_42) | ~r1_tarski(A_42, B_40))), inference(resolution, [status(thm)], [c_6, c_81])).
% 3.27/1.53  tff(c_96, plain, (![B_40, B_2, A_1]: (~v1_xboole_0(B_40) | ~r1_tarski(B_2, B_40) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_93])).
% 3.27/1.53  tff(c_294, plain, (![A_1]: (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_1, '#skF_4'))), inference(resolution, [status(thm)], [c_289, c_96])).
% 3.27/1.53  tff(c_300, plain, (![A_1]: (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~m1_subset_1(A_1, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_294])).
% 3.27/1.53  tff(c_301, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_300])).
% 3.27/1.53  tff(c_273, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_189])).
% 3.27/1.53  tff(c_28, plain, (![B_24, A_22]: (B_24=A_22 | ~r1_tarski(A_22, B_24) | ~v1_zfmisc_1(B_24) | v1_xboole_0(B_24) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.27/1.53  tff(c_292, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_289, c_28])).
% 3.27/1.53  tff(c_297, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_273, c_292])).
% 3.27/1.53  tff(c_302, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_297])).
% 3.27/1.53  tff(c_333, plain, (![A_85, B_86]: (v2_tex_2('#skF_2'(A_85, B_86), A_85) | v3_tex_2(B_86, A_85) | ~v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.27/1.53  tff(c_341, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_333])).
% 3.27/1.53  tff(c_346, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_274, c_341])).
% 3.27/1.53  tff(c_347, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_53, c_346])).
% 3.27/1.53  tff(c_22, plain, (![A_12, B_18]: (m1_subset_1('#skF_2'(A_12, B_18), k1_zfmisc_1(u1_struct_0(A_12))) | v3_tex_2(B_18, A_12) | ~v2_tex_2(B_18, A_12) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.27/1.53  tff(c_435, plain, (![B_99, A_100]: (v1_zfmisc_1(B_99) | ~v2_tex_2(B_99, A_100) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_100))) | v1_xboole_0(B_99) | ~l1_pre_topc(A_100) | ~v2_tdlat_3(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.27/1.53  tff(c_626, plain, (![A_135, B_136]: (v1_zfmisc_1('#skF_2'(A_135, B_136)) | ~v2_tex_2('#skF_2'(A_135, B_136), A_135) | v1_xboole_0('#skF_2'(A_135, B_136)) | ~v2_tdlat_3(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135) | v3_tex_2(B_136, A_135) | ~v2_tex_2(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_22, c_435])).
% 3.27/1.53  tff(c_634, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_347, c_626])).
% 3.27/1.53  tff(c_640, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_274, c_42, c_40, c_634])).
% 3.27/1.53  tff(c_642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_44, c_301, c_302, c_640])).
% 3.27/1.53  tff(c_643, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_297])).
% 3.27/1.53  tff(c_646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_643, c_301])).
% 3.27/1.53  tff(c_649, plain, (![A_137]: (~m1_subset_1(A_137, '#skF_4'))), inference(splitRight, [status(thm)], [c_300])).
% 3.27/1.53  tff(c_653, plain, (~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_14, c_649])).
% 3.27/1.53  tff(c_656, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_653])).
% 3.27/1.53  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_656])).
% 3.27/1.53  tff(c_659, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 3.27/1.53  tff(c_660, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 3.27/1.53  tff(c_732, plain, (![B_159, A_160]: (v2_tex_2(B_159, A_160) | ~v3_tex_2(B_159, A_160) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.27/1.53  tff(c_743, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_732])).
% 3.27/1.53  tff(c_748, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_660, c_743])).
% 3.27/1.53  tff(c_887, plain, (![B_188, A_189]: (v1_zfmisc_1(B_188) | ~v2_tex_2(B_188, A_189) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_189))) | v1_xboole_0(B_188) | ~l1_pre_topc(A_189) | ~v2_tdlat_3(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.27/1.53  tff(c_898, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_887])).
% 3.27/1.53  tff(c_903, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_748, c_898])).
% 3.27/1.53  tff(c_905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_659, c_903])).
% 3.27/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.53  
% 3.27/1.53  Inference rules
% 3.27/1.53  ----------------------
% 3.27/1.53  #Ref     : 0
% 3.27/1.53  #Sup     : 157
% 3.27/1.53  #Fact    : 0
% 3.27/1.53  #Define  : 0
% 3.27/1.53  #Split   : 12
% 3.27/1.53  #Chain   : 0
% 3.27/1.53  #Close   : 0
% 3.27/1.53  
% 3.27/1.53  Ordering : KBO
% 3.27/1.53  
% 3.27/1.53  Simplification rules
% 3.27/1.53  ----------------------
% 3.27/1.53  #Subsume      : 26
% 3.27/1.53  #Demod        : 99
% 3.27/1.53  #Tautology    : 24
% 3.27/1.53  #SimpNegUnit  : 35
% 3.27/1.53  #BackRed      : 0
% 3.27/1.53  
% 3.27/1.53  #Partial instantiations: 0
% 3.27/1.53  #Strategies tried      : 1
% 3.27/1.53  
% 3.27/1.53  Timing (in seconds)
% 3.27/1.53  ----------------------
% 3.27/1.54  Preprocessing        : 0.31
% 3.27/1.54  Parsing              : 0.17
% 3.27/1.54  CNF conversion       : 0.02
% 3.27/1.54  Main loop            : 0.42
% 3.27/1.54  Inferencing          : 0.16
% 3.27/1.54  Reduction            : 0.11
% 3.27/1.54  Demodulation         : 0.07
% 3.27/1.54  BG Simplification    : 0.02
% 3.27/1.54  Subsumption          : 0.08
% 3.27/1.54  Abstraction          : 0.02
% 3.27/1.54  MUC search           : 0.00
% 3.27/1.54  Cooper               : 0.00
% 3.27/1.54  Total                : 0.76
% 3.27/1.54  Index Insertion      : 0.00
% 3.27/1.54  Index Deletion       : 0.00
% 3.27/1.54  Index Matching       : 0.00
% 3.27/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
