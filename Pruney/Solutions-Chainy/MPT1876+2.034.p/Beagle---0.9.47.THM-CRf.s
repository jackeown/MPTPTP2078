%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:55 EST 2020

% Result     : Theorem 6.90s
% Output     : CNFRefutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 985 expanded)
%              Number of leaves         :   44 ( 355 expanded)
%              Depth                    :   32
%              Number of atoms          :  484 (3403 expanded)
%              Number of equality atoms :   18 (  49 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(f_201,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_169,axiom,(
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

tff(f_140,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_181,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_127,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_78,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_81,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_72,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_83,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_72])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_141,plain,(
    ! [A_65,B_66] :
      ( ~ r2_hidden('#skF_2'(A_65,B_66),B_66)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_151,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_141])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_116,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_129,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_116])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_188,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_1'(A_77),B_78)
      | ~ r1_tarski(A_77,B_78)
      | v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_4,c_176])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_200,plain,(
    ! [B_79,A_80] :
      ( ~ v1_xboole_0(B_79)
      | ~ r1_tarski(A_80,B_79)
      | v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_188,c_2])).

tff(c_212,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_129,c_200])).

tff(c_218,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_212])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( m1_subset_1(B_12,A_11)
      | ~ r2_hidden(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_198,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1('#skF_1'(A_77),B_78)
      | v1_xboole_0(B_78)
      | ~ r1_tarski(A_77,B_78)
      | v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_188,c_14])).

tff(c_12,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_153,plain,(
    ! [B_68,A_69] :
      ( m1_subset_1(B_68,A_69)
      | ~ r2_hidden(B_68,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_165,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_153])).

tff(c_219,plain,(
    ! [A_81,B_82] :
      ( k6_domain_1(A_81,B_82) = k1_tarski(B_82)
      | ~ m1_subset_1(B_82,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_232,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = k1_tarski('#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_165,c_219])).

tff(c_278,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1(k6_domain_1(A_87,B_88),k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,A_87)
      | v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4546,plain,(
    ! [A_260] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_260)),k1_zfmisc_1(A_260))
      | ~ m1_subset_1('#skF_1'(A_260),A_260)
      | v1_xboole_0(A_260)
      | v1_xboole_0(A_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_278])).

tff(c_100,plain,(
    ! [B_54,A_55] :
      ( v1_xboole_0(B_54)
      | ~ m1_subset_1(B_54,A_55)
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_109,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_60,c_100])).

tff(c_114,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_109])).

tff(c_344,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1('#skF_2'(A_91,B_92),A_91)
      | v1_xboole_0(A_91)
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_10,c_153])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1425,plain,(
    ! [B_164,B_165] :
      ( r1_tarski('#skF_2'(k1_zfmisc_1(B_164),B_165),B_164)
      | v1_xboole_0(k1_zfmisc_1(B_164))
      | r1_tarski(k1_zfmisc_1(B_164),B_165) ) ),
    inference(resolution,[status(thm)],[c_344,c_22])).

tff(c_552,plain,(
    ! [A_110,B_111,B_112] :
      ( r2_hidden('#skF_2'(A_110,B_111),B_112)
      | ~ r1_tarski(A_110,B_112)
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_10,c_176])).

tff(c_1139,plain,(
    ! [A_151,B_152,B_153] :
      ( m1_subset_1('#skF_2'(A_151,B_152),B_153)
      | v1_xboole_0(B_153)
      | ~ r1_tarski(A_151,B_153)
      | r1_tarski(A_151,B_152) ) ),
    inference(resolution,[status(thm)],[c_552,c_14])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_375,plain,(
    ! [B_95,B_96,A_97] :
      ( r2_hidden(B_95,B_96)
      | ~ r1_tarski(A_97,B_96)
      | ~ m1_subset_1(B_95,A_97)
      | v1_xboole_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_16,c_176])).

tff(c_387,plain,(
    ! [B_95] :
      ( r2_hidden(B_95,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_95,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_129,c_375])).

tff(c_406,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_99,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_387])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_423,plain,(
    ! [A_5] :
      ( r1_tarski(A_5,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_5,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_406,c_8])).

tff(c_1151,plain,(
    ! [A_151] :
      ( v1_xboole_0('#skF_5')
      | ~ r1_tarski(A_151,'#skF_5')
      | r1_tarski(A_151,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1139,c_423])).

tff(c_1234,plain,(
    ! [A_156] :
      ( ~ r1_tarski(A_156,'#skF_5')
      | r1_tarski(A_156,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1151])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_358,plain,(
    ! [A_93,A_94] :
      ( r1_tarski(A_93,A_94)
      | ~ m1_subset_1('#skF_2'(A_93,A_94),A_94)
      | v1_xboole_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_16,c_141])).

tff(c_373,plain,(
    ! [A_93,B_14] :
      ( r1_tarski(A_93,k1_zfmisc_1(B_14))
      | v1_xboole_0(k1_zfmisc_1(B_14))
      | ~ r1_tarski('#skF_2'(A_93,k1_zfmisc_1(B_14)),B_14) ) ),
    inference(resolution,[status(thm)],[c_24,c_358])).

tff(c_1238,plain,(
    ! [A_93] :
      ( r1_tarski(A_93,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'(A_93,k1_zfmisc_1(u1_struct_0('#skF_4'))),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1234,c_373])).

tff(c_1259,plain,(
    ! [A_93] :
      ( r1_tarski(A_93,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'(A_93,k1_zfmisc_1(u1_struct_0('#skF_4'))),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_1238])).

tff(c_1446,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_5'))
    | r1_tarski(k1_zfmisc_1('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_1425,c_1259])).

tff(c_1454,plain,(
    r1_tarski(k1_zfmisc_1('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1446])).

tff(c_183,plain,(
    ! [B_12,B_72,A_11] :
      ( r2_hidden(B_12,B_72)
      | ~ r1_tarski(A_11,B_72)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_176])).

tff(c_1469,plain,(
    ! [B_12] :
      ( r2_hidden(B_12,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_12,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1454,c_183])).

tff(c_1521,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1469])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( v1_xboole_0(B_12)
      | ~ m1_subset_1(B_12,A_11)
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_766,plain,(
    ! [A_124,B_125] :
      ( v1_xboole_0(k6_domain_1(A_124,B_125))
      | ~ v1_xboole_0(k1_zfmisc_1(A_124))
      | ~ m1_subset_1(B_125,A_124)
      | v1_xboole_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_278,c_20])).

tff(c_781,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_tarski('#skF_1'(A_1)))
      | ~ v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_766])).

tff(c_804,plain,(
    ! [A_128] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_128))
      | ~ m1_subset_1('#skF_1'(A_128),A_128)
      | v1_xboole_0(A_128)
      | v1_xboole_0(A_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_781])).

tff(c_808,plain,(
    ! [B_78] :
      ( ~ v1_xboole_0(k1_zfmisc_1(B_78))
      | ~ r1_tarski(B_78,B_78)
      | v1_xboole_0(B_78) ) ),
    inference(resolution,[status(thm)],[c_198,c_804])).

tff(c_830,plain,(
    ! [B_78] :
      ( ~ v1_xboole_0(k1_zfmisc_1(B_78))
      | v1_xboole_0(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_808])).

tff(c_1524,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1521,c_830])).

tff(c_1530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1524])).

tff(c_1537,plain,(
    ! [B_168] :
      ( r2_hidden(B_168,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_168,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_1469])).

tff(c_1542,plain,(
    ! [B_168] :
      ( m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_168,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1537,c_14])).

tff(c_1654,plain,(
    ! [B_172] :
      ( m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_172,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_1542])).

tff(c_54,plain,(
    ! [A_32,B_36] :
      ( v1_pre_topc('#skF_3'(A_32,B_36))
      | ~ v2_tex_2(B_36,A_32)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_32)))
      | v1_xboole_0(B_36)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1664,plain,(
    ! [B_172] :
      ( v1_pre_topc('#skF_3'('#skF_4',B_172))
      | ~ v2_tex_2(B_172,'#skF_4')
      | v1_xboole_0(B_172)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_172,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1654,c_54])).

tff(c_1693,plain,(
    ! [B_172] :
      ( v1_pre_topc('#skF_3'('#skF_4',B_172))
      | ~ v2_tex_2(B_172,'#skF_4')
      | v1_xboole_0(B_172)
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_172,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1664])).

tff(c_1694,plain,(
    ! [B_172] :
      ( v1_pre_topc('#skF_3'('#skF_4',B_172))
      | ~ v2_tex_2(B_172,'#skF_4')
      | v1_xboole_0(B_172)
      | ~ m1_subset_1(B_172,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1693])).

tff(c_4562,plain,
    ( v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4546,c_1694])).

tff(c_4614,plain,
    ( v1_pre_topc('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_62,c_12,c_4562])).

tff(c_4888,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4614])).

tff(c_4891,plain,
    ( ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_198,c_4888])).

tff(c_4900,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_4891])).

tff(c_4902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4900])).

tff(c_4904,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_4614])).

tff(c_1264,plain,(
    ! [B_12,A_156] :
      ( r2_hidden(B_12,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_12,A_156)
      | v1_xboole_0(A_156)
      | ~ r1_tarski(A_156,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1234,c_183])).

tff(c_4910,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_4904,c_1264])).

tff(c_4925,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_4910])).

tff(c_4926,plain,(
    r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4925])).

tff(c_4935,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4926,c_14])).

tff(c_4942,plain,(
    m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_4935])).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4913,plain,
    ( k6_domain_1('#skF_5','#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4904,c_34])).

tff(c_4929,plain,(
    k6_domain_1('#skF_5','#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4913])).

tff(c_295,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(k6_domain_1(A_87,B_88),A_87)
      | ~ m1_subset_1(B_88,A_87)
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_278,c_22])).

tff(c_4978,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),'#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4929,c_295])).

tff(c_5001,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4904,c_4978])).

tff(c_5002,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_5')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_5001])).

tff(c_46,plain,(
    ! [B_31,A_29] :
      ( B_31 = A_29
      | ~ r1_tarski(A_29,B_31)
      | ~ v1_zfmisc_1(B_31)
      | v1_xboole_0(B_31)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5065,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_5002,c_46])).

tff(c_5086,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_5065])).

tff(c_5087,plain,(
    k1_tarski('#skF_1'('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_62,c_5086])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_913,plain,(
    ! [A_133,B_134,B_135] :
      ( r2_hidden('#skF_1'(A_133),B_134)
      | ~ r1_tarski(B_135,B_134)
      | ~ r1_tarski(A_133,B_135)
      | v1_xboole_0(A_133) ) ),
    inference(resolution,[status(thm)],[c_188,c_6])).

tff(c_938,plain,(
    ! [A_136] :
      ( r2_hidden('#skF_1'(A_136),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_136,'#skF_5')
      | v1_xboole_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_129,c_913])).

tff(c_943,plain,(
    ! [A_136] :
      ( m1_subset_1('#skF_1'(A_136),u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_136,'#skF_5')
      | v1_xboole_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_938,c_14])).

tff(c_952,plain,(
    ! [A_137] :
      ( m1_subset_1('#skF_1'(A_137),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_137,'#skF_5')
      | v1_xboole_0(A_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_943])).

tff(c_955,plain,(
    ! [A_137] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_137)) = k1_tarski('#skF_1'(A_137))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_137,'#skF_5')
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_952,c_34])).

tff(c_3010,plain,(
    ! [A_210] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_210)) = k1_tarski('#skF_1'(A_210))
      | ~ r1_tarski(A_210,'#skF_5')
      | v1_xboole_0(A_210) ) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_955])).

tff(c_58,plain,(
    ! [A_38,B_40] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_38),B_40),A_38)
      | ~ m1_subset_1(B_40,u1_struct_0(A_38))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_3019,plain,(
    ! [A_210] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_210)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_210),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_210,'#skF_5')
      | v1_xboole_0(A_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3010,c_58])).

tff(c_3046,plain,(
    ! [A_210] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_210)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_210),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_210,'#skF_5')
      | v1_xboole_0(A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_3019])).

tff(c_3047,plain,(
    ! [A_210] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_210)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_210),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_210,'#skF_5')
      | v1_xboole_0(A_210) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3046])).

tff(c_5102,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5087,c_3047])).

tff(c_5135,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_4942,c_5102])).

tff(c_5137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_83,c_5135])).

tff(c_5138,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_6569,plain,(
    ! [A_394,B_395] :
      ( m1_pre_topc('#skF_3'(A_394,B_395),A_394)
      | ~ v2_tex_2(B_395,A_394)
      | ~ m1_subset_1(B_395,k1_zfmisc_1(u1_struct_0(A_394)))
      | v1_xboole_0(B_395)
      | ~ l1_pre_topc(A_394)
      | ~ v2_pre_topc(A_394)
      | v2_struct_0(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_6596,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_6569])).

tff(c_6614,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_5138,c_6596])).

tff(c_6615,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_6614])).

tff(c_28,plain,(
    ! [B_18,A_16] :
      ( l1_pre_topc(B_18)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6621,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6615,c_28])).

tff(c_6628,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6621])).

tff(c_26,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6191,plain,(
    ! [A_375,B_376] :
      ( ~ v2_struct_0('#skF_3'(A_375,B_376))
      | ~ v2_tex_2(B_376,A_375)
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0(A_375)))
      | v1_xboole_0(B_376)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_6224,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_6191])).

tff(c_6241,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_5138,c_6224])).

tff(c_6242,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_6241])).

tff(c_66,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_44,plain,(
    ! [B_28,A_26] :
      ( v2_tdlat_3(B_28)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6618,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6615,c_44])).

tff(c_6624,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_6618])).

tff(c_6625,plain,(
    v2_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6624])).

tff(c_36,plain,(
    ! [A_24] :
      ( v2_pre_topc(A_24)
      | ~ v2_tdlat_3(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6632,plain,
    ( v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6625,c_36])).

tff(c_6668,plain,(
    v2_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6628,c_6632])).

tff(c_6403,plain,(
    ! [A_387,B_388] :
      ( v1_tdlat_3('#skF_3'(A_387,B_388))
      | ~ v2_tex_2(B_388,A_387)
      | ~ m1_subset_1(B_388,k1_zfmisc_1(u1_struct_0(A_387)))
      | v1_xboole_0(B_388)
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387)
      | v2_struct_0(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_6440,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_6403])).

tff(c_6458,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_5138,c_6440])).

tff(c_6459,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_6458])).

tff(c_40,plain,(
    ! [A_25] :
      ( v7_struct_0(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v1_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5139,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_6704,plain,(
    ! [A_398,B_399] :
      ( u1_struct_0('#skF_3'(A_398,B_399)) = B_399
      | ~ v2_tex_2(B_399,A_398)
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0(A_398)))
      | v1_xboole_0(B_399)
      | ~ l1_pre_topc(A_398)
      | ~ v2_pre_topc(A_398)
      | v2_struct_0(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_6741,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_6704])).

tff(c_6759,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_5138,c_6741])).

tff(c_6760,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_6759])).

tff(c_30,plain,(
    ! [A_19] :
      ( v1_zfmisc_1(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | ~ v7_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6781,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6760,c_30])).

tff(c_6802,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_5139,c_6781])).

tff(c_6804,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6802])).

tff(c_6807,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_6804])).

tff(c_6810,plain,(
    v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6628,c_6668,c_6459,c_6625,c_6807])).

tff(c_6812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6242,c_6810])).

tff(c_6813,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6802])).

tff(c_6851,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_26,c_6813])).

tff(c_6855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6628,c_6851])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.90/2.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.46  
% 6.90/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.46  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 6.90/2.46  
% 6.90/2.46  %Foreground sorts:
% 6.90/2.46  
% 6.90/2.46  
% 6.90/2.46  %Background operators:
% 6.90/2.46  
% 6.90/2.46  
% 6.90/2.46  %Foreground operators:
% 6.90/2.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.90/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.90/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.90/2.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.90/2.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.90/2.46  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 6.90/2.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.90/2.46  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 6.90/2.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.90/2.46  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.90/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.90/2.46  tff('#skF_5', type, '#skF_5': $i).
% 6.90/2.46  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.90/2.46  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.90/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.90/2.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.90/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.90/2.46  tff('#skF_4', type, '#skF_4': $i).
% 6.90/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.90/2.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.90/2.46  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 6.90/2.46  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.90/2.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.90/2.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.90/2.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.90/2.46  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 6.90/2.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.90/2.46  
% 6.90/2.49  tff(f_201, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 6.90/2.49  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.90/2.49  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.90/2.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.90/2.49  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.90/2.49  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 6.90/2.49  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.90/2.49  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 6.90/2.49  tff(f_169, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 6.90/2.49  tff(f_140, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 6.90/2.49  tff(f_181, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 6.90/2.49  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.90/2.49  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.90/2.49  tff(f_127, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 6.90/2.49  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 6.90/2.49  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_1)).
% 6.90/2.49  tff(f_75, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 6.90/2.49  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.90/2.49  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.90/2.49  tff(c_62, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.90/2.49  tff(c_68, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.90/2.49  tff(c_78, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.90/2.49  tff(c_81, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_78])).
% 6.90/2.49  tff(c_72, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.90/2.49  tff(c_83, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_72])).
% 6.90/2.49  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.90/2.49  tff(c_141, plain, (![A_65, B_66]: (~r2_hidden('#skF_2'(A_65, B_66), B_66) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.90/2.49  tff(c_151, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_141])).
% 6.90/2.49  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.90/2.49  tff(c_116, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.90/2.49  tff(c_129, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_116])).
% 6.90/2.49  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.90/2.49  tff(c_176, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.90/2.49  tff(c_188, plain, (![A_77, B_78]: (r2_hidden('#skF_1'(A_77), B_78) | ~r1_tarski(A_77, B_78) | v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_4, c_176])).
% 6.90/2.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.90/2.49  tff(c_200, plain, (![B_79, A_80]: (~v1_xboole_0(B_79) | ~r1_tarski(A_80, B_79) | v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_188, c_2])).
% 6.90/2.49  tff(c_212, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_129, c_200])).
% 6.90/2.49  tff(c_218, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_212])).
% 6.90/2.49  tff(c_14, plain, (![B_12, A_11]: (m1_subset_1(B_12, A_11) | ~r2_hidden(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.90/2.49  tff(c_198, plain, (![A_77, B_78]: (m1_subset_1('#skF_1'(A_77), B_78) | v1_xboole_0(B_78) | ~r1_tarski(A_77, B_78) | v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_188, c_14])).
% 6.90/2.49  tff(c_12, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.90/2.49  tff(c_153, plain, (![B_68, A_69]: (m1_subset_1(B_68, A_69) | ~r2_hidden(B_68, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.90/2.49  tff(c_165, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_153])).
% 6.90/2.49  tff(c_219, plain, (![A_81, B_82]: (k6_domain_1(A_81, B_82)=k1_tarski(B_82) | ~m1_subset_1(B_82, A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.90/2.49  tff(c_232, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=k1_tarski('#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_165, c_219])).
% 6.90/2.49  tff(c_278, plain, (![A_87, B_88]: (m1_subset_1(k6_domain_1(A_87, B_88), k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, A_87) | v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.90/2.49  tff(c_4546, plain, (![A_260]: (m1_subset_1(k1_tarski('#skF_1'(A_260)), k1_zfmisc_1(A_260)) | ~m1_subset_1('#skF_1'(A_260), A_260) | v1_xboole_0(A_260) | v1_xboole_0(A_260))), inference(superposition, [status(thm), theory('equality')], [c_232, c_278])).
% 6.90/2.49  tff(c_100, plain, (![B_54, A_55]: (v1_xboole_0(B_54) | ~m1_subset_1(B_54, A_55) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.90/2.49  tff(c_109, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_60, c_100])).
% 6.90/2.49  tff(c_114, plain, (~v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_62, c_109])).
% 6.90/2.49  tff(c_344, plain, (![A_91, B_92]: (m1_subset_1('#skF_2'(A_91, B_92), A_91) | v1_xboole_0(A_91) | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_10, c_153])).
% 6.90/2.49  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.90/2.49  tff(c_1425, plain, (![B_164, B_165]: (r1_tarski('#skF_2'(k1_zfmisc_1(B_164), B_165), B_164) | v1_xboole_0(k1_zfmisc_1(B_164)) | r1_tarski(k1_zfmisc_1(B_164), B_165))), inference(resolution, [status(thm)], [c_344, c_22])).
% 6.90/2.49  tff(c_552, plain, (![A_110, B_111, B_112]: (r2_hidden('#skF_2'(A_110, B_111), B_112) | ~r1_tarski(A_110, B_112) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_10, c_176])).
% 6.90/2.49  tff(c_1139, plain, (![A_151, B_152, B_153]: (m1_subset_1('#skF_2'(A_151, B_152), B_153) | v1_xboole_0(B_153) | ~r1_tarski(A_151, B_153) | r1_tarski(A_151, B_152))), inference(resolution, [status(thm)], [c_552, c_14])).
% 6.90/2.49  tff(c_16, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.90/2.49  tff(c_375, plain, (![B_95, B_96, A_97]: (r2_hidden(B_95, B_96) | ~r1_tarski(A_97, B_96) | ~m1_subset_1(B_95, A_97) | v1_xboole_0(A_97))), inference(resolution, [status(thm)], [c_16, c_176])).
% 6.90/2.49  tff(c_387, plain, (![B_95]: (r2_hidden(B_95, u1_struct_0('#skF_4')) | ~m1_subset_1(B_95, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_129, c_375])).
% 6.90/2.49  tff(c_406, plain, (![B_99]: (r2_hidden(B_99, u1_struct_0('#skF_4')) | ~m1_subset_1(B_99, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_387])).
% 6.90/2.49  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.90/2.49  tff(c_423, plain, (![A_5]: (r1_tarski(A_5, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_5, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_406, c_8])).
% 6.90/2.49  tff(c_1151, plain, (![A_151]: (v1_xboole_0('#skF_5') | ~r1_tarski(A_151, '#skF_5') | r1_tarski(A_151, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1139, c_423])).
% 6.90/2.49  tff(c_1234, plain, (![A_156]: (~r1_tarski(A_156, '#skF_5') | r1_tarski(A_156, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_62, c_1151])).
% 6.90/2.49  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.90/2.49  tff(c_358, plain, (![A_93, A_94]: (r1_tarski(A_93, A_94) | ~m1_subset_1('#skF_2'(A_93, A_94), A_94) | v1_xboole_0(A_94))), inference(resolution, [status(thm)], [c_16, c_141])).
% 6.90/2.49  tff(c_373, plain, (![A_93, B_14]: (r1_tarski(A_93, k1_zfmisc_1(B_14)) | v1_xboole_0(k1_zfmisc_1(B_14)) | ~r1_tarski('#skF_2'(A_93, k1_zfmisc_1(B_14)), B_14))), inference(resolution, [status(thm)], [c_24, c_358])).
% 6.90/2.49  tff(c_1238, plain, (![A_93]: (r1_tarski(A_93, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'(A_93, k1_zfmisc_1(u1_struct_0('#skF_4'))), '#skF_5'))), inference(resolution, [status(thm)], [c_1234, c_373])).
% 6.90/2.49  tff(c_1259, plain, (![A_93]: (r1_tarski(A_93, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'(A_93, k1_zfmisc_1(u1_struct_0('#skF_4'))), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_114, c_1238])).
% 6.90/2.49  tff(c_1446, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5')) | r1_tarski(k1_zfmisc_1('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1425, c_1259])).
% 6.90/2.49  tff(c_1454, plain, (r1_tarski(k1_zfmisc_1('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_1446])).
% 6.90/2.49  tff(c_183, plain, (![B_12, B_72, A_11]: (r2_hidden(B_12, B_72) | ~r1_tarski(A_11, B_72) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_16, c_176])).
% 6.90/2.49  tff(c_1469, plain, (![B_12]: (r2_hidden(B_12, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_12, k1_zfmisc_1('#skF_5')) | v1_xboole_0(k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_1454, c_183])).
% 6.90/2.49  tff(c_1521, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1469])).
% 6.90/2.49  tff(c_20, plain, (![B_12, A_11]: (v1_xboole_0(B_12) | ~m1_subset_1(B_12, A_11) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.90/2.49  tff(c_766, plain, (![A_124, B_125]: (v1_xboole_0(k6_domain_1(A_124, B_125)) | ~v1_xboole_0(k1_zfmisc_1(A_124)) | ~m1_subset_1(B_125, A_124) | v1_xboole_0(A_124))), inference(resolution, [status(thm)], [c_278, c_20])).
% 6.90/2.49  tff(c_781, plain, (![A_1]: (v1_xboole_0(k1_tarski('#skF_1'(A_1))) | ~v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1) | v1_xboole_0(A_1))), inference(superposition, [status(thm), theory('equality')], [c_232, c_766])).
% 6.90/2.49  tff(c_804, plain, (![A_128]: (~v1_xboole_0(k1_zfmisc_1(A_128)) | ~m1_subset_1('#skF_1'(A_128), A_128) | v1_xboole_0(A_128) | v1_xboole_0(A_128))), inference(negUnitSimplification, [status(thm)], [c_12, c_781])).
% 6.90/2.49  tff(c_808, plain, (![B_78]: (~v1_xboole_0(k1_zfmisc_1(B_78)) | ~r1_tarski(B_78, B_78) | v1_xboole_0(B_78))), inference(resolution, [status(thm)], [c_198, c_804])).
% 6.90/2.49  tff(c_830, plain, (![B_78]: (~v1_xboole_0(k1_zfmisc_1(B_78)) | v1_xboole_0(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_808])).
% 6.90/2.49  tff(c_1524, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1521, c_830])).
% 6.90/2.49  tff(c_1530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1524])).
% 6.90/2.49  tff(c_1537, plain, (![B_168]: (r2_hidden(B_168, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_168, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_1469])).
% 6.90/2.49  tff(c_1542, plain, (![B_168]: (m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_168, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_1537, c_14])).
% 6.90/2.49  tff(c_1654, plain, (![B_172]: (m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_172, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_114, c_1542])).
% 6.90/2.49  tff(c_54, plain, (![A_32, B_36]: (v1_pre_topc('#skF_3'(A_32, B_36)) | ~v2_tex_2(B_36, A_32) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_32))) | v1_xboole_0(B_36) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_169])).
% 6.90/2.49  tff(c_1664, plain, (![B_172]: (v1_pre_topc('#skF_3'('#skF_4', B_172)) | ~v2_tex_2(B_172, '#skF_4') | v1_xboole_0(B_172) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(B_172, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_1654, c_54])).
% 6.90/2.49  tff(c_1693, plain, (![B_172]: (v1_pre_topc('#skF_3'('#skF_4', B_172)) | ~v2_tex_2(B_172, '#skF_4') | v1_xboole_0(B_172) | v2_struct_0('#skF_4') | ~m1_subset_1(B_172, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1664])).
% 6.90/2.49  tff(c_1694, plain, (![B_172]: (v1_pre_topc('#skF_3'('#skF_4', B_172)) | ~v2_tex_2(B_172, '#skF_4') | v1_xboole_0(B_172) | ~m1_subset_1(B_172, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_70, c_1693])).
% 6.90/2.49  tff(c_4562, plain, (v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4546, c_1694])).
% 6.90/2.49  tff(c_4614, plain, (v1_pre_topc('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_62, c_12, c_4562])).
% 6.90/2.49  tff(c_4888, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_4614])).
% 6.90/2.49  tff(c_4891, plain, (~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_198, c_4888])).
% 6.90/2.49  tff(c_4900, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_4891])).
% 6.90/2.49  tff(c_4902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_4900])).
% 6.90/2.49  tff(c_4904, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_4614])).
% 6.90/2.49  tff(c_1264, plain, (![B_12, A_156]: (r2_hidden(B_12, u1_struct_0('#skF_4')) | ~m1_subset_1(B_12, A_156) | v1_xboole_0(A_156) | ~r1_tarski(A_156, '#skF_5'))), inference(resolution, [status(thm)], [c_1234, c_183])).
% 6.90/2.49  tff(c_4910, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5') | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_4904, c_1264])).
% 6.90/2.49  tff(c_4925, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_4910])).
% 6.90/2.49  tff(c_4926, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_4925])).
% 6.90/2.49  tff(c_4935, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4926, c_14])).
% 6.90/2.49  tff(c_4942, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_218, c_4935])).
% 6.90/2.49  tff(c_34, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.90/2.49  tff(c_4913, plain, (k6_domain_1('#skF_5', '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4904, c_34])).
% 6.90/2.49  tff(c_4929, plain, (k6_domain_1('#skF_5', '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_4913])).
% 6.90/2.49  tff(c_295, plain, (![A_87, B_88]: (r1_tarski(k6_domain_1(A_87, B_88), A_87) | ~m1_subset_1(B_88, A_87) | v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_278, c_22])).
% 6.90/2.49  tff(c_4978, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4929, c_295])).
% 6.90/2.49  tff(c_5001, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), '#skF_5') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4904, c_4978])).
% 6.90/2.49  tff(c_5002, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_5001])).
% 6.90/2.49  tff(c_46, plain, (![B_31, A_29]: (B_31=A_29 | ~r1_tarski(A_29, B_31) | ~v1_zfmisc_1(B_31) | v1_xboole_0(B_31) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.90/2.49  tff(c_5065, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))), inference(resolution, [status(thm)], [c_5002, c_46])).
% 6.90/2.49  tff(c_5086, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_5065])).
% 6.90/2.49  tff(c_5087, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_12, c_62, c_5086])).
% 6.90/2.49  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.90/2.49  tff(c_913, plain, (![A_133, B_134, B_135]: (r2_hidden('#skF_1'(A_133), B_134) | ~r1_tarski(B_135, B_134) | ~r1_tarski(A_133, B_135) | v1_xboole_0(A_133))), inference(resolution, [status(thm)], [c_188, c_6])).
% 6.90/2.49  tff(c_938, plain, (![A_136]: (r2_hidden('#skF_1'(A_136), u1_struct_0('#skF_4')) | ~r1_tarski(A_136, '#skF_5') | v1_xboole_0(A_136))), inference(resolution, [status(thm)], [c_129, c_913])).
% 6.90/2.49  tff(c_943, plain, (![A_136]: (m1_subset_1('#skF_1'(A_136), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(A_136, '#skF_5') | v1_xboole_0(A_136))), inference(resolution, [status(thm)], [c_938, c_14])).
% 6.90/2.49  tff(c_952, plain, (![A_137]: (m1_subset_1('#skF_1'(A_137), u1_struct_0('#skF_4')) | ~r1_tarski(A_137, '#skF_5') | v1_xboole_0(A_137))), inference(negUnitSimplification, [status(thm)], [c_218, c_943])).
% 6.90/2.49  tff(c_955, plain, (![A_137]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_137))=k1_tarski('#skF_1'(A_137)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(A_137, '#skF_5') | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_952, c_34])).
% 6.90/2.49  tff(c_3010, plain, (![A_210]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_210))=k1_tarski('#skF_1'(A_210)) | ~r1_tarski(A_210, '#skF_5') | v1_xboole_0(A_210))), inference(negUnitSimplification, [status(thm)], [c_218, c_955])).
% 6.90/2.49  tff(c_58, plain, (![A_38, B_40]: (v2_tex_2(k6_domain_1(u1_struct_0(A_38), B_40), A_38) | ~m1_subset_1(B_40, u1_struct_0(A_38)) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.90/2.49  tff(c_3019, plain, (![A_210]: (v2_tex_2(k1_tarski('#skF_1'(A_210)), '#skF_4') | ~m1_subset_1('#skF_1'(A_210), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_210, '#skF_5') | v1_xboole_0(A_210))), inference(superposition, [status(thm), theory('equality')], [c_3010, c_58])).
% 6.90/2.49  tff(c_3046, plain, (![A_210]: (v2_tex_2(k1_tarski('#skF_1'(A_210)), '#skF_4') | ~m1_subset_1('#skF_1'(A_210), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r1_tarski(A_210, '#skF_5') | v1_xboole_0(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_3019])).
% 6.90/2.49  tff(c_3047, plain, (![A_210]: (v2_tex_2(k1_tarski('#skF_1'(A_210)), '#skF_4') | ~m1_subset_1('#skF_1'(A_210), u1_struct_0('#skF_4')) | ~r1_tarski(A_210, '#skF_5') | v1_xboole_0(A_210))), inference(negUnitSimplification, [status(thm)], [c_70, c_3046])).
% 6.90/2.49  tff(c_5102, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5087, c_3047])).
% 6.90/2.49  tff(c_5135, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_4942, c_5102])).
% 6.90/2.49  tff(c_5137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_83, c_5135])).
% 6.90/2.49  tff(c_5138, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_78])).
% 6.90/2.49  tff(c_6569, plain, (![A_394, B_395]: (m1_pre_topc('#skF_3'(A_394, B_395), A_394) | ~v2_tex_2(B_395, A_394) | ~m1_subset_1(B_395, k1_zfmisc_1(u1_struct_0(A_394))) | v1_xboole_0(B_395) | ~l1_pre_topc(A_394) | ~v2_pre_topc(A_394) | v2_struct_0(A_394))), inference(cnfTransformation, [status(thm)], [f_169])).
% 6.90/2.49  tff(c_6596, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_6569])).
% 6.90/2.49  tff(c_6614, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_5138, c_6596])).
% 6.90/2.49  tff(c_6615, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_62, c_6614])).
% 6.90/2.49  tff(c_28, plain, (![B_18, A_16]: (l1_pre_topc(B_18) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.90/2.49  tff(c_6621, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6615, c_28])).
% 6.90/2.49  tff(c_6628, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6621])).
% 6.90/2.49  tff(c_26, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.90/2.49  tff(c_6191, plain, (![A_375, B_376]: (~v2_struct_0('#skF_3'(A_375, B_376)) | ~v2_tex_2(B_376, A_375) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0(A_375))) | v1_xboole_0(B_376) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375))), inference(cnfTransformation, [status(thm)], [f_169])).
% 6.90/2.49  tff(c_6224, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_6191])).
% 6.90/2.49  tff(c_6241, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_5138, c_6224])).
% 6.90/2.49  tff(c_6242, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_62, c_6241])).
% 6.90/2.49  tff(c_66, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.90/2.49  tff(c_44, plain, (![B_28, A_26]: (v2_tdlat_3(B_28) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26) | ~v2_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.90/2.49  tff(c_6618, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_6615, c_44])).
% 6.90/2.49  tff(c_6624, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_6618])).
% 6.90/2.49  tff(c_6625, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_6624])).
% 6.90/2.49  tff(c_36, plain, (![A_24]: (v2_pre_topc(A_24) | ~v2_tdlat_3(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.90/2.49  tff(c_6632, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_6625, c_36])).
% 6.90/2.49  tff(c_6668, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6628, c_6632])).
% 6.90/2.49  tff(c_6403, plain, (![A_387, B_388]: (v1_tdlat_3('#skF_3'(A_387, B_388)) | ~v2_tex_2(B_388, A_387) | ~m1_subset_1(B_388, k1_zfmisc_1(u1_struct_0(A_387))) | v1_xboole_0(B_388) | ~l1_pre_topc(A_387) | ~v2_pre_topc(A_387) | v2_struct_0(A_387))), inference(cnfTransformation, [status(thm)], [f_169])).
% 6.90/2.49  tff(c_6440, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_6403])).
% 6.90/2.49  tff(c_6458, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_5138, c_6440])).
% 6.90/2.49  tff(c_6459, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_62, c_6458])).
% 6.90/2.49  tff(c_40, plain, (![A_25]: (v7_struct_0(A_25) | ~v2_tdlat_3(A_25) | ~v1_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.90/2.49  tff(c_5139, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 6.90/2.49  tff(c_6704, plain, (![A_398, B_399]: (u1_struct_0('#skF_3'(A_398, B_399))=B_399 | ~v2_tex_2(B_399, A_398) | ~m1_subset_1(B_399, k1_zfmisc_1(u1_struct_0(A_398))) | v1_xboole_0(B_399) | ~l1_pre_topc(A_398) | ~v2_pre_topc(A_398) | v2_struct_0(A_398))), inference(cnfTransformation, [status(thm)], [f_169])).
% 6.90/2.49  tff(c_6741, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_6704])).
% 6.90/2.49  tff(c_6759, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_5138, c_6741])).
% 6.90/2.49  tff(c_6760, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_70, c_62, c_6759])).
% 6.90/2.49  tff(c_30, plain, (![A_19]: (v1_zfmisc_1(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | ~v7_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.90/2.49  tff(c_6781, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6760, c_30])).
% 6.90/2.49  tff(c_6802, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_5139, c_6781])).
% 6.90/2.49  tff(c_6804, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_6802])).
% 6.90/2.49  tff(c_6807, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_6804])).
% 6.90/2.49  tff(c_6810, plain, (v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6628, c_6668, c_6459, c_6625, c_6807])).
% 6.90/2.49  tff(c_6812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6242, c_6810])).
% 6.90/2.49  tff(c_6813, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_6802])).
% 6.90/2.49  tff(c_6851, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_26, c_6813])).
% 6.90/2.49  tff(c_6855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6628, c_6851])).
% 6.90/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.90/2.49  
% 6.90/2.49  Inference rules
% 6.90/2.49  ----------------------
% 6.90/2.49  #Ref     : 0
% 6.90/2.49  #Sup     : 1382
% 6.90/2.49  #Fact    : 0
% 6.90/2.49  #Define  : 0
% 6.90/2.49  #Split   : 27
% 6.90/2.49  #Chain   : 0
% 6.90/2.49  #Close   : 0
% 6.90/2.49  
% 6.90/2.49  Ordering : KBO
% 6.90/2.49  
% 6.90/2.49  Simplification rules
% 6.90/2.49  ----------------------
% 6.90/2.49  #Subsume      : 319
% 6.90/2.49  #Demod        : 289
% 6.90/2.49  #Tautology    : 311
% 6.90/2.49  #SimpNegUnit  : 557
% 6.90/2.49  #BackRed      : 2
% 6.90/2.49  
% 6.90/2.49  #Partial instantiations: 0
% 6.90/2.49  #Strategies tried      : 1
% 6.90/2.49  
% 6.90/2.49  Timing (in seconds)
% 6.90/2.49  ----------------------
% 6.90/2.49  Preprocessing        : 0.37
% 6.90/2.49  Parsing              : 0.20
% 6.90/2.49  CNF conversion       : 0.03
% 6.90/2.49  Main loop            : 1.27
% 6.90/2.49  Inferencing          : 0.42
% 6.90/2.49  Reduction            : 0.37
% 6.90/2.49  Demodulation         : 0.21
% 6.90/2.49  BG Simplification    : 0.05
% 6.90/2.49  Subsumption          : 0.34
% 6.90/2.49  Abstraction          : 0.06
% 6.90/2.49  MUC search           : 0.00
% 6.90/2.49  Cooper               : 0.00
% 6.90/2.49  Total                : 1.69
% 6.90/2.49  Index Insertion      : 0.00
% 6.90/2.49  Index Deletion       : 0.00
% 6.90/2.49  Index Matching       : 0.00
% 6.90/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
