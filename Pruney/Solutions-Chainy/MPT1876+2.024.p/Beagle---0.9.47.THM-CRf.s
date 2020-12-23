%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:53 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 235 expanded)
%              Number of leaves         :   40 ( 101 expanded)
%              Depth                    :   12
%              Number of atoms          :  274 ( 853 expanded)
%              Number of equality atoms :   14 (  23 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_183,negated_conjecture,(
    ~ ! [A] :
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
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_34,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_163,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) )
           => ( ~ v2_struct_0(B)
              & ~ v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(c_20,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_66,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_69,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_72,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_60])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_134,plain,(
    ! [A_63,C_64,B_65] :
      ( m1_subset_1(A_63,C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_140,plain,(
    ! [A_63] :
      ( m1_subset_1(A_63,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_63,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_134])).

tff(c_6,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_tarski(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_186,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(A_76,B_75)
      | ~ v1_zfmisc_1(B_75)
      | v1_xboole_0(B_75)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_192,plain,(
    ! [A_6,B_7] :
      ( k1_tarski(A_6) = B_7
      | ~ v1_zfmisc_1(B_7)
      | v1_xboole_0(B_7)
      | v1_xboole_0(k1_tarski(A_6))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_186])).

tff(c_217,plain,(
    ! [A_80,B_81] :
      ( k1_tarski(A_80) = B_81
      | ~ v1_zfmisc_1(B_81)
      | v1_xboole_0(B_81)
      | ~ r2_hidden(A_80,B_81) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_192])).

tff(c_222,plain,(
    ! [A_82] :
      ( k1_tarski('#skF_1'(A_82)) = A_82
      | ~ v1_zfmisc_1(A_82)
      | v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_4,c_217])).

tff(c_103,plain,(
    ! [B_57,A_58] :
      ( v1_xboole_0(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_109,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_103])).

tff(c_113,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_109])).

tff(c_141,plain,(
    ! [A_66] :
      ( m1_subset_1(A_66,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_134])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( k6_domain_1(A_21,B_22) = k1_tarski(B_22)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_144,plain,(
    ! [A_66] :
      ( k6_domain_1(u1_struct_0('#skF_3'),A_66) = k1_tarski(A_66)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_141,c_26])).

tff(c_147,plain,(
    ! [A_66] :
      ( k6_domain_1(u1_struct_0('#skF_3'),A_66) = k1_tarski(A_66)
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_144])).

tff(c_204,plain,(
    ! [A_77,B_78] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_77),B_78),A_77)
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_207,plain,(
    ! [A_66] :
      ( v2_tex_2(k1_tarski(A_66),'#skF_3')
      | ~ m1_subset_1(A_66,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_204])).

tff(c_209,plain,(
    ! [A_66] :
      ( v2_tex_2(k1_tarski(A_66),'#skF_3')
      | ~ m1_subset_1(A_66,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_207])).

tff(c_210,plain,(
    ! [A_66] :
      ( v2_tex_2(k1_tarski(A_66),'#skF_3')
      | ~ m1_subset_1(A_66,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_209])).

tff(c_326,plain,(
    ! [A_95] :
      ( v2_tex_2(A_95,'#skF_3')
      | ~ m1_subset_1('#skF_1'(A_95),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'(A_95),'#skF_4')
      | ~ v1_zfmisc_1(A_95)
      | v1_xboole_0(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_210])).

tff(c_390,plain,(
    ! [A_104] :
      ( v2_tex_2(A_104,'#skF_3')
      | ~ v1_zfmisc_1(A_104)
      | v1_xboole_0(A_104)
      | ~ r2_hidden('#skF_1'(A_104),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_140,c_326])).

tff(c_398,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_390])).

tff(c_402,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_398])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_72,c_402])).

tff(c_405,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_709,plain,(
    ! [A_165,B_166] :
      ( ~ v2_struct_0('#skF_2'(A_165,B_166))
      | ~ v2_tex_2(B_166,A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | v1_xboole_0(B_166)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_720,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_709])).

tff(c_725,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_405,c_720])).

tff(c_726,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_725])).

tff(c_406,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_948,plain,(
    ! [A_191,B_192] :
      ( u1_struct_0('#skF_2'(A_191,B_192)) = B_192
      | ~ v2_tex_2(B_192,A_191)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | v1_xboole_0(B_192)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_963,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_948])).

tff(c_969,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_405,c_963])).

tff(c_970,plain,(
    u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_969])).

tff(c_24,plain,(
    ! [A_20] :
      ( v1_zfmisc_1(u1_struct_0(A_20))
      | ~ l1_struct_0(A_20)
      | ~ v7_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_989,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_24])).

tff(c_998,plain,
    ( ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_989])).

tff(c_1000,plain,(
    ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_998])).

tff(c_54,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_847,plain,(
    ! [A_182,B_183] :
      ( v1_tdlat_3('#skF_2'(A_182,B_183))
      | ~ v2_tex_2(B_183,A_182)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | v1_xboole_0(B_183)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_858,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_847])).

tff(c_863,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_405,c_858])).

tff(c_864,plain,(
    v1_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_863])).

tff(c_1167,plain,(
    ! [A_200,B_201] :
      ( m1_pre_topc('#skF_2'(A_200,B_201),A_200)
      | ~ v2_tex_2(B_201,A_200)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | v1_xboole_0(B_201)
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1183,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1167])).

tff(c_1191,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_405,c_1183])).

tff(c_1192,plain,(
    m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_1191])).

tff(c_30,plain,(
    ! [B_26,A_24] :
      ( ~ v1_tdlat_3(B_26)
      | v7_struct_0(B_26)
      | v2_struct_0(B_26)
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24)
      | ~ v2_tdlat_3(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1195,plain,
    ( ~ v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v7_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1192,c_30])).

tff(c_1201,plain,
    ( v7_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_864,c_1195])).

tff(c_1203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_726,c_1000,c_1201])).

tff(c_1204,plain,(
    ~ l1_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_998])).

tff(c_1209,plain,(
    ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_1204])).

tff(c_1368,plain,(
    ! [A_208,B_209] :
      ( m1_pre_topc('#skF_2'(A_208,B_209),A_208)
      | ~ v2_tex_2(B_209,A_208)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_208)))
      | v1_xboole_0(B_209)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1384,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1368])).

tff(c_1392,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_405,c_1384])).

tff(c_1393,plain,(
    m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_1392])).

tff(c_22,plain,(
    ! [B_19,A_17] :
      ( l1_pre_topc(B_19)
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1399,plain,
    ( l1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1393,c_22])).

tff(c_1406,plain,(
    l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1399])).

tff(c_1408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1209,c_1406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:41:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.62  
% 3.56/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.62  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.56/1.62  
% 3.56/1.62  %Foreground sorts:
% 3.56/1.62  
% 3.56/1.62  
% 3.56/1.62  %Background operators:
% 3.56/1.62  
% 3.56/1.62  
% 3.56/1.62  %Foreground operators:
% 3.56/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.56/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.56/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.56/1.62  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.56/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.56/1.62  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.56/1.62  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.56/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.62  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.56/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.62  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.56/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.62  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.56/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.56/1.62  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.56/1.62  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.56/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.56/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.56/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.62  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.56/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.62  
% 3.94/1.64  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.94/1.64  tff(f_183, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.94/1.64  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.94/1.64  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.94/1.64  tff(f_34, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.94/1.64  tff(f_38, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.94/1.64  tff(f_122, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.94/1.64  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.94/1.64  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.94/1.64  tff(f_163, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 3.94/1.64  tff(f_151, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 3.94/1.64  tff(f_72, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.94/1.64  tff(f_109, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 3.94/1.64  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.94/1.64  tff(c_20, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.94/1.64  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.94/1.64  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.94/1.64  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.94/1.64  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.94/1.64  tff(c_66, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.94/1.64  tff(c_69, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_66])).
% 3.94/1.64  tff(c_60, plain, (~v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.94/1.64  tff(c_72, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_60])).
% 3.94/1.64  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.94/1.64  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.94/1.64  tff(c_134, plain, (![A_63, C_64, B_65]: (m1_subset_1(A_63, C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_63, B_65))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.94/1.64  tff(c_140, plain, (![A_63]: (m1_subset_1(A_63, u1_struct_0('#skF_3')) | ~r2_hidden(A_63, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_134])).
% 3.94/1.64  tff(c_6, plain, (![A_5]: (~v1_xboole_0(k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.94/1.64  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.94/1.64  tff(c_186, plain, (![B_75, A_76]: (B_75=A_76 | ~r1_tarski(A_76, B_75) | ~v1_zfmisc_1(B_75) | v1_xboole_0(B_75) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.94/1.64  tff(c_192, plain, (![A_6, B_7]: (k1_tarski(A_6)=B_7 | ~v1_zfmisc_1(B_7) | v1_xboole_0(B_7) | v1_xboole_0(k1_tarski(A_6)) | ~r2_hidden(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_186])).
% 3.94/1.64  tff(c_217, plain, (![A_80, B_81]: (k1_tarski(A_80)=B_81 | ~v1_zfmisc_1(B_81) | v1_xboole_0(B_81) | ~r2_hidden(A_80, B_81))), inference(negUnitSimplification, [status(thm)], [c_6, c_192])).
% 3.94/1.64  tff(c_222, plain, (![A_82]: (k1_tarski('#skF_1'(A_82))=A_82 | ~v1_zfmisc_1(A_82) | v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_4, c_217])).
% 3.94/1.64  tff(c_103, plain, (![B_57, A_58]: (v1_xboole_0(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.94/1.64  tff(c_109, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_103])).
% 3.94/1.64  tff(c_113, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_109])).
% 3.94/1.64  tff(c_141, plain, (![A_66]: (m1_subset_1(A_66, u1_struct_0('#skF_3')) | ~r2_hidden(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_134])).
% 3.94/1.64  tff(c_26, plain, (![A_21, B_22]: (k6_domain_1(A_21, B_22)=k1_tarski(B_22) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.94/1.64  tff(c_144, plain, (![A_66]: (k6_domain_1(u1_struct_0('#skF_3'), A_66)=k1_tarski(A_66) | v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_141, c_26])).
% 3.94/1.64  tff(c_147, plain, (![A_66]: (k6_domain_1(u1_struct_0('#skF_3'), A_66)=k1_tarski(A_66) | ~r2_hidden(A_66, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_113, c_144])).
% 3.94/1.64  tff(c_204, plain, (![A_77, B_78]: (v2_tex_2(k6_domain_1(u1_struct_0(A_77), B_78), A_77) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.94/1.64  tff(c_207, plain, (![A_66]: (v2_tex_2(k1_tarski(A_66), '#skF_3') | ~m1_subset_1(A_66, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(A_66, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_204])).
% 3.94/1.64  tff(c_209, plain, (![A_66]: (v2_tex_2(k1_tarski(A_66), '#skF_3') | ~m1_subset_1(A_66, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r2_hidden(A_66, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_207])).
% 3.94/1.64  tff(c_210, plain, (![A_66]: (v2_tex_2(k1_tarski(A_66), '#skF_3') | ~m1_subset_1(A_66, u1_struct_0('#skF_3')) | ~r2_hidden(A_66, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_209])).
% 3.94/1.64  tff(c_326, plain, (![A_95]: (v2_tex_2(A_95, '#skF_3') | ~m1_subset_1('#skF_1'(A_95), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'(A_95), '#skF_4') | ~v1_zfmisc_1(A_95) | v1_xboole_0(A_95))), inference(superposition, [status(thm), theory('equality')], [c_222, c_210])).
% 3.94/1.64  tff(c_390, plain, (![A_104]: (v2_tex_2(A_104, '#skF_3') | ~v1_zfmisc_1(A_104) | v1_xboole_0(A_104) | ~r2_hidden('#skF_1'(A_104), '#skF_4'))), inference(resolution, [status(thm)], [c_140, c_326])).
% 3.94/1.64  tff(c_398, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_390])).
% 3.94/1.64  tff(c_402, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_398])).
% 3.94/1.64  tff(c_404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_72, c_402])).
% 3.94/1.64  tff(c_405, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 3.94/1.64  tff(c_709, plain, (![A_165, B_166]: (~v2_struct_0('#skF_2'(A_165, B_166)) | ~v2_tex_2(B_166, A_165) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | v1_xboole_0(B_166) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.94/1.64  tff(c_720, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_709])).
% 3.94/1.64  tff(c_725, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_405, c_720])).
% 3.94/1.64  tff(c_726, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_725])).
% 3.94/1.64  tff(c_406, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_66])).
% 3.94/1.64  tff(c_948, plain, (![A_191, B_192]: (u1_struct_0('#skF_2'(A_191, B_192))=B_192 | ~v2_tex_2(B_192, A_191) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_191))) | v1_xboole_0(B_192) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.94/1.64  tff(c_963, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_948])).
% 3.94/1.64  tff(c_969, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_405, c_963])).
% 3.94/1.64  tff(c_970, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_969])).
% 3.94/1.64  tff(c_24, plain, (![A_20]: (v1_zfmisc_1(u1_struct_0(A_20)) | ~l1_struct_0(A_20) | ~v7_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.94/1.64  tff(c_989, plain, (v1_zfmisc_1('#skF_4') | ~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_970, c_24])).
% 3.94/1.64  tff(c_998, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_406, c_989])).
% 3.94/1.64  tff(c_1000, plain, (~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_998])).
% 3.94/1.64  tff(c_54, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.94/1.64  tff(c_847, plain, (![A_182, B_183]: (v1_tdlat_3('#skF_2'(A_182, B_183)) | ~v2_tex_2(B_183, A_182) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | v1_xboole_0(B_183) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.94/1.64  tff(c_858, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_847])).
% 3.94/1.64  tff(c_863, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_405, c_858])).
% 3.94/1.64  tff(c_864, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_863])).
% 3.94/1.64  tff(c_1167, plain, (![A_200, B_201]: (m1_pre_topc('#skF_2'(A_200, B_201), A_200) | ~v2_tex_2(B_201, A_200) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | v1_xboole_0(B_201) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.94/1.64  tff(c_1183, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1167])).
% 3.94/1.64  tff(c_1191, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_405, c_1183])).
% 3.94/1.64  tff(c_1192, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_1191])).
% 3.94/1.64  tff(c_30, plain, (![B_26, A_24]: (~v1_tdlat_3(B_26) | v7_struct_0(B_26) | v2_struct_0(B_26) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24) | ~v2_tdlat_3(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.94/1.64  tff(c_1195, plain, (~v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v7_struct_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1192, c_30])).
% 3.94/1.64  tff(c_1201, plain, (v7_struct_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_864, c_1195])).
% 3.94/1.64  tff(c_1203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_726, c_1000, c_1201])).
% 3.94/1.64  tff(c_1204, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_998])).
% 3.94/1.64  tff(c_1209, plain, (~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_1204])).
% 3.94/1.64  tff(c_1368, plain, (![A_208, B_209]: (m1_pre_topc('#skF_2'(A_208, B_209), A_208) | ~v2_tex_2(B_209, A_208) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_208))) | v1_xboole_0(B_209) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.94/1.64  tff(c_1384, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1368])).
% 3.94/1.64  tff(c_1392, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_405, c_1384])).
% 3.94/1.64  tff(c_1393, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_1392])).
% 3.94/1.64  tff(c_22, plain, (![B_19, A_17]: (l1_pre_topc(B_19) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.94/1.64  tff(c_1399, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1393, c_22])).
% 3.94/1.64  tff(c_1406, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1399])).
% 3.94/1.64  tff(c_1408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1209, c_1406])).
% 3.94/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.64  
% 3.94/1.64  Inference rules
% 3.94/1.64  ----------------------
% 3.94/1.64  #Ref     : 0
% 3.94/1.64  #Sup     : 272
% 3.94/1.64  #Fact    : 0
% 3.94/1.64  #Define  : 0
% 3.94/1.64  #Split   : 8
% 3.94/1.64  #Chain   : 0
% 3.94/1.64  #Close   : 0
% 3.94/1.64  
% 3.94/1.64  Ordering : KBO
% 3.94/1.64  
% 3.94/1.64  Simplification rules
% 3.94/1.64  ----------------------
% 3.94/1.64  #Subsume      : 50
% 3.94/1.64  #Demod        : 47
% 3.94/1.64  #Tautology    : 64
% 3.94/1.64  #SimpNegUnit  : 71
% 3.94/1.64  #BackRed      : 0
% 3.94/1.64  
% 3.94/1.64  #Partial instantiations: 0
% 3.94/1.64  #Strategies tried      : 1
% 3.94/1.64  
% 3.94/1.64  Timing (in seconds)
% 3.94/1.64  ----------------------
% 3.94/1.64  Preprocessing        : 0.35
% 3.94/1.64  Parsing              : 0.18
% 3.94/1.64  CNF conversion       : 0.03
% 3.94/1.64  Main loop            : 0.53
% 3.94/1.64  Inferencing          : 0.21
% 3.94/1.64  Reduction            : 0.14
% 3.94/1.64  Demodulation         : 0.09
% 3.94/1.64  BG Simplification    : 0.03
% 3.94/1.64  Subsumption          : 0.11
% 3.94/1.65  Abstraction          : 0.03
% 3.94/1.65  MUC search           : 0.00
% 3.94/1.65  Cooper               : 0.00
% 3.94/1.65  Total                : 0.93
% 3.94/1.65  Index Insertion      : 0.00
% 3.94/1.65  Index Deletion       : 0.00
% 3.94/1.65  Index Matching       : 0.00
% 3.94/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
