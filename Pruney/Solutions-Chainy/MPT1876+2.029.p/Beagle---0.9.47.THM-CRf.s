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
% DateTime   : Thu Dec  3 10:29:54 EST 2020

% Result     : Theorem 4.79s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 752 expanded)
%              Number of leaves         :   44 ( 275 expanded)
%              Depth                    :   26
%              Number of atoms          :  378 (2395 expanded)
%              Number of equality atoms :   18 (  64 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_204,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_143,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_184,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_172,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_72,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_76,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_85,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_86,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_82])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_tarski(A_11),B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_310,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(A_94,B_93)
      | ~ v1_zfmisc_1(B_93)
      | v1_xboole_0(B_93)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_325,plain,(
    ! [A_11,B_12] :
      ( k1_tarski(A_11) = B_12
      | ~ v1_zfmisc_1(B_12)
      | v1_xboole_0(B_12)
      | v1_xboole_0(k1_tarski(A_11))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_310])).

tff(c_357,plain,(
    ! [A_98,B_99] :
      ( k1_tarski(A_98) = B_99
      | ~ v1_zfmisc_1(B_99)
      | v1_xboole_0(B_99)
      | ~ r2_hidden(A_98,B_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_325])).

tff(c_380,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_357])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_126,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_139,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_126])).

tff(c_212,plain,(
    ! [C_79,B_80,A_81] :
      ( r2_hidden(C_79,B_80)
      | ~ r2_hidden(C_79,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_227,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85),B_86)
      | ~ r1_tarski(A_85,B_86)
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_4,c_212])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_277,plain,(
    ! [B_90,A_91] :
      ( ~ v1_xboole_0(B_90)
      | ~ r1_tarski(A_91,B_90)
      | v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_227,c_2])).

tff(c_289,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_139,c_277])).

tff(c_298,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_289])).

tff(c_156,plain,(
    ! [B_71,A_72] :
      ( m1_subset_1(B_71,A_72)
      | ~ r2_hidden(B_71,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_168,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_156])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(B_14,A_13)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_512,plain,(
    ! [B_114,B_115,A_116] :
      ( r2_hidden(B_114,B_115)
      | ~ r1_tarski(A_116,B_115)
      | ~ m1_subset_1(B_114,A_116)
      | v1_xboole_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_20,c_212])).

tff(c_524,plain,(
    ! [B_114,B_12,A_11] :
      ( r2_hidden(B_114,B_12)
      | ~ m1_subset_1(B_114,k1_tarski(A_11))
      | v1_xboole_0(k1_tarski(A_11))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_512])).

tff(c_604,plain,(
    ! [B_122,B_123,A_124] :
      ( r2_hidden(B_122,B_123)
      | ~ m1_subset_1(B_122,k1_tarski(A_124))
      | ~ r2_hidden(A_124,B_123) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_524])).

tff(c_612,plain,(
    ! [A_124,B_123] :
      ( r2_hidden('#skF_1'(k1_tarski(A_124)),B_123)
      | ~ r2_hidden(A_124,B_123)
      | v1_xboole_0(k1_tarski(A_124)) ) ),
    inference(resolution,[status(thm)],[c_168,c_604])).

tff(c_638,plain,(
    ! [A_126,B_127] :
      ( r2_hidden('#skF_1'(k1_tarski(A_126)),B_127)
      | ~ r2_hidden(A_126,B_127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_612])).

tff(c_335,plain,(
    ! [A_11,B_12] :
      ( k1_tarski(A_11) = B_12
      | ~ v1_zfmisc_1(B_12)
      | v1_xboole_0(B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_325])).

tff(c_1470,plain,(
    ! [A_171,B_172] :
      ( k1_tarski('#skF_1'(k1_tarski(A_171))) = B_172
      | ~ v1_zfmisc_1(B_172)
      | v1_xboole_0(B_172)
      | ~ r2_hidden(A_171,B_172) ) ),
    inference(resolution,[status(thm)],[c_638,c_335])).

tff(c_1757,plain,(
    ! [A_178] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_178)))) = A_178
      | ~ v1_zfmisc_1(A_178)
      | v1_xboole_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_4,c_1470])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_169,plain,(
    ! [A_73,B_74] :
      ( ~ r2_hidden('#skF_2'(A_73,B_74),B_74)
      | r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_180,plain,(
    ! [A_75] : r1_tarski(A_75,A_75) ),
    inference(resolution,[status(thm)],[c_10,c_169])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | ~ r1_tarski(k1_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_186,plain,(
    ! [A_76] : r2_hidden(A_76,k1_tarski(A_76)) ),
    inference(resolution,[status(thm)],[c_180,c_14])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( m1_subset_1(B_14,A_13)
      | ~ r2_hidden(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_189,plain,(
    ! [A_76] :
      ( m1_subset_1(A_76,k1_tarski(A_76))
      | v1_xboole_0(k1_tarski(A_76)) ) ),
    inference(resolution,[status(thm)],[c_186,c_18])).

tff(c_195,plain,(
    ! [A_76] : m1_subset_1(A_76,k1_tarski(A_76)) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_189])).

tff(c_1905,plain,(
    ! [A_180] :
      ( m1_subset_1('#skF_1'(k1_tarski('#skF_1'(A_180))),A_180)
      | ~ v1_zfmisc_1(A_180)
      | v1_xboole_0(A_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1757,c_195])).

tff(c_522,plain,(
    ! [B_114] :
      ( r2_hidden(B_114,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_114,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_139,c_512])).

tff(c_531,plain,(
    ! [B_114] :
      ( r2_hidden(B_114,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_114,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_522])).

tff(c_185,plain,(
    ! [A_11] : r2_hidden(A_11,k1_tarski(A_11)) ),
    inference(resolution,[status(thm)],[c_180,c_14])).

tff(c_381,plain,(
    ! [A_100] :
      ( k1_tarski('#skF_1'(A_100)) = A_100
      | ~ v1_zfmisc_1(A_100)
      | v1_xboole_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_4,c_357])).

tff(c_728,plain,(
    ! [A_136,B_137] :
      ( r1_tarski(A_136,B_137)
      | ~ r2_hidden('#skF_1'(A_136),B_137)
      | ~ v1_zfmisc_1(A_136)
      | v1_xboole_0(A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_16])).

tff(c_758,plain,(
    ! [A_138] :
      ( r1_tarski(A_138,k1_tarski('#skF_1'(A_138)))
      | ~ v1_zfmisc_1(A_138)
      | v1_xboole_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_185,c_728])).

tff(c_775,plain,(
    ! [A_11] :
      ( r2_hidden(A_11,k1_tarski('#skF_1'(k1_tarski(A_11))))
      | ~ v1_zfmisc_1(k1_tarski(A_11))
      | v1_xboole_0(k1_tarski(A_11)) ) ),
    inference(resolution,[status(thm)],[c_758,c_14])).

tff(c_790,plain,(
    ! [A_139] :
      ( r2_hidden(A_139,k1_tarski('#skF_1'(k1_tarski(A_139))))
      | ~ v1_zfmisc_1(k1_tarski(A_139)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_775])).

tff(c_802,plain,(
    ! [A_139] :
      ( m1_subset_1(A_139,k1_tarski('#skF_1'(k1_tarski(A_139))))
      | v1_xboole_0(k1_tarski('#skF_1'(k1_tarski(A_139))))
      | ~ v1_zfmisc_1(k1_tarski(A_139)) ) ),
    inference(resolution,[status(thm)],[c_790,c_18])).

tff(c_828,plain,(
    ! [A_141] :
      ( m1_subset_1(A_141,k1_tarski('#skF_1'(k1_tarski(A_141))))
      | ~ v1_zfmisc_1(k1_tarski(A_141)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_802])).

tff(c_534,plain,(
    ! [B_114,B_12,A_11] :
      ( r2_hidden(B_114,B_12)
      | ~ m1_subset_1(B_114,k1_tarski(A_11))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_524])).

tff(c_1045,plain,(
    ! [A_152,B_153] :
      ( r2_hidden(A_152,B_153)
      | ~ r2_hidden('#skF_1'(k1_tarski(A_152)),B_153)
      | ~ v1_zfmisc_1(k1_tarski(A_152)) ) ),
    inference(resolution,[status(thm)],[c_828,c_534])).

tff(c_1087,plain,(
    ! [A_152] :
      ( r2_hidden(A_152,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(k1_tarski(A_152))
      | ~ m1_subset_1('#skF_1'(k1_tarski(A_152)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_531,c_1045])).

tff(c_1909,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1905,c_1087])).

tff(c_1949,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1909])).

tff(c_1950,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1949])).

tff(c_1964,plain,(
    ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1950])).

tff(c_1967,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_1964])).

tff(c_1969,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_86,c_1967])).

tff(c_1971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1969])).

tff(c_1972,plain,(
    r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1950])).

tff(c_1992,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1972,c_18])).

tff(c_2007,plain,(
    m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_1992])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2057,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2007,c_36])).

tff(c_2065,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_2057])).

tff(c_62,plain,(
    ! [A_39,B_41] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_39),B_41),A_39)
      | ~ m1_subset_1(B_41,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2157,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2065,c_62])).

tff(c_2167,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2007,c_2157])).

tff(c_2168,plain,(
    v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2167])).

tff(c_2174,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_2168])).

tff(c_2176,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2174])).

tff(c_2178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_85,c_2176])).

tff(c_2180,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3148,plain,(
    ! [A_294,B_295] :
      ( m1_pre_topc('#skF_3'(A_294,B_295),A_294)
      | ~ v2_tex_2(B_295,A_294)
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0(A_294)))
      | v1_xboole_0(B_295)
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_3168,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_3148])).

tff(c_3177,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2180,c_3168])).

tff(c_3178,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_3177])).

tff(c_32,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3184,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_3178,c_32])).

tff(c_3191,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3184])).

tff(c_30,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2870,plain,(
    ! [A_280,B_281] :
      ( ~ v2_struct_0('#skF_3'(A_280,B_281))
      | ~ v2_tex_2(B_281,A_280)
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0(A_280)))
      | v1_xboole_0(B_281)
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_2893,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2870])).

tff(c_2901,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2180,c_2893])).

tff(c_2902,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_2901])).

tff(c_70,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_48,plain,(
    ! [B_29,A_27] :
      ( v2_tdlat_3(B_29)
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_tdlat_3(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3181,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3178,c_48])).

tff(c_3187,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_3181])).

tff(c_3188,plain,(
    v2_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3187])).

tff(c_40,plain,(
    ! [A_25] :
      ( v2_pre_topc(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3195,plain,
    ( v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_3188,c_40])).

tff(c_3197,plain,(
    v2_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3191,c_3195])).

tff(c_2602,plain,(
    ! [A_257,B_258] :
      ( v1_tdlat_3('#skF_3'(A_257,B_258))
      | ~ v2_tex_2(B_258,A_257)
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0(A_257)))
      | v1_xboole_0(B_258)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_2621,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2602])).

tff(c_2628,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2180,c_2621])).

tff(c_2629,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_2628])).

tff(c_44,plain,(
    ! [A_26] :
      ( v7_struct_0(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v1_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2179,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3348,plain,(
    ! [A_302,B_303] :
      ( u1_struct_0('#skF_3'(A_302,B_303)) = B_303
      | ~ v2_tex_2(B_303,A_302)
      | ~ m1_subset_1(B_303,k1_zfmisc_1(u1_struct_0(A_302)))
      | v1_xboole_0(B_303)
      | ~ l1_pre_topc(A_302)
      | ~ v2_pre_topc(A_302)
      | v2_struct_0(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_3375,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_3348])).

tff(c_3384,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2180,c_3375])).

tff(c_3385,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_3384])).

tff(c_34,plain,(
    ! [A_21] :
      ( v1_zfmisc_1(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | ~ v7_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3406,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3385,c_34])).

tff(c_3427,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_2179,c_3406])).

tff(c_3429,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3427])).

tff(c_3432,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_3429])).

tff(c_3435,plain,(
    v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3191,c_3197,c_2629,c_3188,c_3432])).

tff(c_3437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2902,c_3435])).

tff(c_3438,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3427])).

tff(c_3448,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_30,c_3438])).

tff(c_3452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3191,c_3448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.79/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/1.90  
% 4.79/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/1.91  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 4.79/1.91  
% 4.79/1.91  %Foreground sorts:
% 4.79/1.91  
% 4.79/1.91  
% 4.79/1.91  %Background operators:
% 4.79/1.91  
% 4.79/1.91  
% 4.79/1.91  %Foreground operators:
% 4.79/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.79/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.79/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.79/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.79/1.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.79/1.91  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 4.79/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.79/1.91  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.79/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.79/1.91  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.79/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.79/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.79/1.91  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.79/1.91  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.79/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.79/1.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.79/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.79/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.79/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.79/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.79/1.91  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.79/1.91  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.79/1.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.79/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.79/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.79/1.91  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.79/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.79/1.91  
% 5.14/1.93  tff(f_204, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 5.14/1.93  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.14/1.93  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 5.14/1.93  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.14/1.93  tff(f_143, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 5.14/1.93  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.14/1.93  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.14/1.93  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.14/1.93  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.14/1.93  tff(f_184, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 5.14/1.93  tff(f_172, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 5.14/1.93  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.14/1.93  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.14/1.93  tff(f_130, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 5.14/1.93  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 5.14/1.93  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 5.14/1.93  tff(f_79, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 5.14/1.93  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.14/1.93  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.14/1.93  tff(c_66, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.14/1.93  tff(c_72, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.14/1.93  tff(c_76, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.14/1.93  tff(c_85, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_76])).
% 5.14/1.93  tff(c_82, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.14/1.93  tff(c_86, plain, (v1_zfmisc_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_85, c_82])).
% 5.14/1.93  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/1.93  tff(c_12, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.14/1.93  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.14/1.93  tff(c_310, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(A_94, B_93) | ~v1_zfmisc_1(B_93) | v1_xboole_0(B_93) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.14/1.93  tff(c_325, plain, (![A_11, B_12]: (k1_tarski(A_11)=B_12 | ~v1_zfmisc_1(B_12) | v1_xboole_0(B_12) | v1_xboole_0(k1_tarski(A_11)) | ~r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_310])).
% 5.14/1.93  tff(c_357, plain, (![A_98, B_99]: (k1_tarski(A_98)=B_99 | ~v1_zfmisc_1(B_99) | v1_xboole_0(B_99) | ~r2_hidden(A_98, B_99))), inference(negUnitSimplification, [status(thm)], [c_12, c_325])).
% 5.14/1.93  tff(c_380, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_357])).
% 5.14/1.93  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.14/1.93  tff(c_126, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.14/1.93  tff(c_139, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_126])).
% 5.14/1.93  tff(c_212, plain, (![C_79, B_80, A_81]: (r2_hidden(C_79, B_80) | ~r2_hidden(C_79, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.14/1.93  tff(c_227, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85), B_86) | ~r1_tarski(A_85, B_86) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_4, c_212])).
% 5.14/1.93  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/1.93  tff(c_277, plain, (![B_90, A_91]: (~v1_xboole_0(B_90) | ~r1_tarski(A_91, B_90) | v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_227, c_2])).
% 5.14/1.93  tff(c_289, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_139, c_277])).
% 5.14/1.93  tff(c_298, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_289])).
% 5.14/1.93  tff(c_156, plain, (![B_71, A_72]: (m1_subset_1(B_71, A_72) | ~r2_hidden(B_71, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.14/1.93  tff(c_168, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_156])).
% 5.14/1.93  tff(c_20, plain, (![B_14, A_13]: (r2_hidden(B_14, A_13) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.14/1.93  tff(c_512, plain, (![B_114, B_115, A_116]: (r2_hidden(B_114, B_115) | ~r1_tarski(A_116, B_115) | ~m1_subset_1(B_114, A_116) | v1_xboole_0(A_116))), inference(resolution, [status(thm)], [c_20, c_212])).
% 5.14/1.93  tff(c_524, plain, (![B_114, B_12, A_11]: (r2_hidden(B_114, B_12) | ~m1_subset_1(B_114, k1_tarski(A_11)) | v1_xboole_0(k1_tarski(A_11)) | ~r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_512])).
% 5.14/1.93  tff(c_604, plain, (![B_122, B_123, A_124]: (r2_hidden(B_122, B_123) | ~m1_subset_1(B_122, k1_tarski(A_124)) | ~r2_hidden(A_124, B_123))), inference(negUnitSimplification, [status(thm)], [c_12, c_524])).
% 5.14/1.93  tff(c_612, plain, (![A_124, B_123]: (r2_hidden('#skF_1'(k1_tarski(A_124)), B_123) | ~r2_hidden(A_124, B_123) | v1_xboole_0(k1_tarski(A_124)))), inference(resolution, [status(thm)], [c_168, c_604])).
% 5.14/1.93  tff(c_638, plain, (![A_126, B_127]: (r2_hidden('#skF_1'(k1_tarski(A_126)), B_127) | ~r2_hidden(A_126, B_127))), inference(negUnitSimplification, [status(thm)], [c_12, c_612])).
% 5.14/1.93  tff(c_335, plain, (![A_11, B_12]: (k1_tarski(A_11)=B_12 | ~v1_zfmisc_1(B_12) | v1_xboole_0(B_12) | ~r2_hidden(A_11, B_12))), inference(negUnitSimplification, [status(thm)], [c_12, c_325])).
% 5.14/1.93  tff(c_1470, plain, (![A_171, B_172]: (k1_tarski('#skF_1'(k1_tarski(A_171)))=B_172 | ~v1_zfmisc_1(B_172) | v1_xboole_0(B_172) | ~r2_hidden(A_171, B_172))), inference(resolution, [status(thm)], [c_638, c_335])).
% 5.14/1.93  tff(c_1757, plain, (![A_178]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_178))))=A_178 | ~v1_zfmisc_1(A_178) | v1_xboole_0(A_178))), inference(resolution, [status(thm)], [c_4, c_1470])).
% 5.14/1.93  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.14/1.93  tff(c_169, plain, (![A_73, B_74]: (~r2_hidden('#skF_2'(A_73, B_74), B_74) | r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.14/1.93  tff(c_180, plain, (![A_75]: (r1_tarski(A_75, A_75))), inference(resolution, [status(thm)], [c_10, c_169])).
% 5.14/1.93  tff(c_14, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | ~r1_tarski(k1_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.14/1.93  tff(c_186, plain, (![A_76]: (r2_hidden(A_76, k1_tarski(A_76)))), inference(resolution, [status(thm)], [c_180, c_14])).
% 5.14/1.93  tff(c_18, plain, (![B_14, A_13]: (m1_subset_1(B_14, A_13) | ~r2_hidden(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.14/1.93  tff(c_189, plain, (![A_76]: (m1_subset_1(A_76, k1_tarski(A_76)) | v1_xboole_0(k1_tarski(A_76)))), inference(resolution, [status(thm)], [c_186, c_18])).
% 5.14/1.93  tff(c_195, plain, (![A_76]: (m1_subset_1(A_76, k1_tarski(A_76)))), inference(negUnitSimplification, [status(thm)], [c_12, c_189])).
% 5.14/1.93  tff(c_1905, plain, (![A_180]: (m1_subset_1('#skF_1'(k1_tarski('#skF_1'(A_180))), A_180) | ~v1_zfmisc_1(A_180) | v1_xboole_0(A_180))), inference(superposition, [status(thm), theory('equality')], [c_1757, c_195])).
% 5.14/1.93  tff(c_522, plain, (![B_114]: (r2_hidden(B_114, u1_struct_0('#skF_4')) | ~m1_subset_1(B_114, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_139, c_512])).
% 5.14/1.93  tff(c_531, plain, (![B_114]: (r2_hidden(B_114, u1_struct_0('#skF_4')) | ~m1_subset_1(B_114, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_522])).
% 5.14/1.93  tff(c_185, plain, (![A_11]: (r2_hidden(A_11, k1_tarski(A_11)))), inference(resolution, [status(thm)], [c_180, c_14])).
% 5.14/1.93  tff(c_381, plain, (![A_100]: (k1_tarski('#skF_1'(A_100))=A_100 | ~v1_zfmisc_1(A_100) | v1_xboole_0(A_100))), inference(resolution, [status(thm)], [c_4, c_357])).
% 5.14/1.93  tff(c_728, plain, (![A_136, B_137]: (r1_tarski(A_136, B_137) | ~r2_hidden('#skF_1'(A_136), B_137) | ~v1_zfmisc_1(A_136) | v1_xboole_0(A_136))), inference(superposition, [status(thm), theory('equality')], [c_381, c_16])).
% 5.14/1.93  tff(c_758, plain, (![A_138]: (r1_tarski(A_138, k1_tarski('#skF_1'(A_138))) | ~v1_zfmisc_1(A_138) | v1_xboole_0(A_138))), inference(resolution, [status(thm)], [c_185, c_728])).
% 5.14/1.93  tff(c_775, plain, (![A_11]: (r2_hidden(A_11, k1_tarski('#skF_1'(k1_tarski(A_11)))) | ~v1_zfmisc_1(k1_tarski(A_11)) | v1_xboole_0(k1_tarski(A_11)))), inference(resolution, [status(thm)], [c_758, c_14])).
% 5.14/1.93  tff(c_790, plain, (![A_139]: (r2_hidden(A_139, k1_tarski('#skF_1'(k1_tarski(A_139)))) | ~v1_zfmisc_1(k1_tarski(A_139)))), inference(negUnitSimplification, [status(thm)], [c_12, c_775])).
% 5.14/1.93  tff(c_802, plain, (![A_139]: (m1_subset_1(A_139, k1_tarski('#skF_1'(k1_tarski(A_139)))) | v1_xboole_0(k1_tarski('#skF_1'(k1_tarski(A_139)))) | ~v1_zfmisc_1(k1_tarski(A_139)))), inference(resolution, [status(thm)], [c_790, c_18])).
% 5.14/1.93  tff(c_828, plain, (![A_141]: (m1_subset_1(A_141, k1_tarski('#skF_1'(k1_tarski(A_141)))) | ~v1_zfmisc_1(k1_tarski(A_141)))), inference(negUnitSimplification, [status(thm)], [c_12, c_802])).
% 5.14/1.93  tff(c_534, plain, (![B_114, B_12, A_11]: (r2_hidden(B_114, B_12) | ~m1_subset_1(B_114, k1_tarski(A_11)) | ~r2_hidden(A_11, B_12))), inference(negUnitSimplification, [status(thm)], [c_12, c_524])).
% 5.14/1.93  tff(c_1045, plain, (![A_152, B_153]: (r2_hidden(A_152, B_153) | ~r2_hidden('#skF_1'(k1_tarski(A_152)), B_153) | ~v1_zfmisc_1(k1_tarski(A_152)))), inference(resolution, [status(thm)], [c_828, c_534])).
% 5.14/1.93  tff(c_1087, plain, (![A_152]: (r2_hidden(A_152, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski(A_152)) | ~m1_subset_1('#skF_1'(k1_tarski(A_152)), '#skF_5'))), inference(resolution, [status(thm)], [c_531, c_1045])).
% 5.14/1.93  tff(c_1909, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1905, c_1087])).
% 5.14/1.93  tff(c_1949, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1909])).
% 5.14/1.93  tff(c_1950, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1949])).
% 5.14/1.93  tff(c_1964, plain, (~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(splitLeft, [status(thm)], [c_1950])).
% 5.14/1.93  tff(c_1967, plain, (~v1_zfmisc_1('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_380, c_1964])).
% 5.14/1.93  tff(c_1969, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_86, c_1967])).
% 5.14/1.93  tff(c_1971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1969])).
% 5.14/1.93  tff(c_1972, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1950])).
% 5.14/1.93  tff(c_1992, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1972, c_18])).
% 5.14/1.93  tff(c_2007, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_298, c_1992])).
% 5.14/1.93  tff(c_36, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.14/1.93  tff(c_2057, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2007, c_36])).
% 5.14/1.93  tff(c_2065, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_298, c_2057])).
% 5.14/1.93  tff(c_62, plain, (![A_39, B_41]: (v2_tex_2(k6_domain_1(u1_struct_0(A_39), B_41), A_39) | ~m1_subset_1(B_41, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_184])).
% 5.14/1.93  tff(c_2157, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2065, c_62])).
% 5.14/1.93  tff(c_2167, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2007, c_2157])).
% 5.14/1.93  tff(c_2168, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_2167])).
% 5.14/1.93  tff(c_2174, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_380, c_2168])).
% 5.14/1.93  tff(c_2176, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2174])).
% 5.14/1.93  tff(c_2178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_85, c_2176])).
% 5.14/1.93  tff(c_2180, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_76])).
% 5.14/1.93  tff(c_3148, plain, (![A_294, B_295]: (m1_pre_topc('#skF_3'(A_294, B_295), A_294) | ~v2_tex_2(B_295, A_294) | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0(A_294))) | v1_xboole_0(B_295) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.14/1.93  tff(c_3168, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_3148])).
% 5.14/1.93  tff(c_3177, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2180, c_3168])).
% 5.14/1.93  tff(c_3178, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_3177])).
% 5.14/1.93  tff(c_32, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.14/1.93  tff(c_3184, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_3178, c_32])).
% 5.14/1.93  tff(c_3191, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3184])).
% 5.14/1.93  tff(c_30, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.14/1.93  tff(c_2870, plain, (![A_280, B_281]: (~v2_struct_0('#skF_3'(A_280, B_281)) | ~v2_tex_2(B_281, A_280) | ~m1_subset_1(B_281, k1_zfmisc_1(u1_struct_0(A_280))) | v1_xboole_0(B_281) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.14/1.93  tff(c_2893, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2870])).
% 5.14/1.93  tff(c_2901, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2180, c_2893])).
% 5.14/1.93  tff(c_2902, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_2901])).
% 5.14/1.93  tff(c_70, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.14/1.93  tff(c_48, plain, (![B_29, A_27]: (v2_tdlat_3(B_29) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27) | ~v2_tdlat_3(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.14/1.93  tff(c_3181, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_3178, c_48])).
% 5.14/1.93  tff(c_3187, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_3181])).
% 5.14/1.93  tff(c_3188, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_3187])).
% 5.14/1.93  tff(c_40, plain, (![A_25]: (v2_pre_topc(A_25) | ~v2_tdlat_3(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.14/1.93  tff(c_3195, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_3188, c_40])).
% 5.14/1.93  tff(c_3197, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3191, c_3195])).
% 5.14/1.93  tff(c_2602, plain, (![A_257, B_258]: (v1_tdlat_3('#skF_3'(A_257, B_258)) | ~v2_tex_2(B_258, A_257) | ~m1_subset_1(B_258, k1_zfmisc_1(u1_struct_0(A_257))) | v1_xboole_0(B_258) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257) | v2_struct_0(A_257))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.14/1.93  tff(c_2621, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2602])).
% 5.14/1.93  tff(c_2628, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2180, c_2621])).
% 5.14/1.93  tff(c_2629, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_2628])).
% 5.14/1.93  tff(c_44, plain, (![A_26]: (v7_struct_0(A_26) | ~v2_tdlat_3(A_26) | ~v1_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.14/1.93  tff(c_2179, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_76])).
% 5.14/1.93  tff(c_3348, plain, (![A_302, B_303]: (u1_struct_0('#skF_3'(A_302, B_303))=B_303 | ~v2_tex_2(B_303, A_302) | ~m1_subset_1(B_303, k1_zfmisc_1(u1_struct_0(A_302))) | v1_xboole_0(B_303) | ~l1_pre_topc(A_302) | ~v2_pre_topc(A_302) | v2_struct_0(A_302))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.14/1.93  tff(c_3375, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_3348])).
% 5.14/1.93  tff(c_3384, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2180, c_3375])).
% 5.14/1.93  tff(c_3385, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_3384])).
% 5.14/1.93  tff(c_34, plain, (![A_21]: (v1_zfmisc_1(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | ~v7_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.14/1.93  tff(c_3406, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3385, c_34])).
% 5.14/1.93  tff(c_3427, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2179, c_3406])).
% 5.14/1.93  tff(c_3429, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_3427])).
% 5.14/1.93  tff(c_3432, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_3429])).
% 5.14/1.93  tff(c_3435, plain, (v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3191, c_3197, c_2629, c_3188, c_3432])).
% 5.14/1.93  tff(c_3437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2902, c_3435])).
% 5.14/1.93  tff(c_3438, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_3427])).
% 5.14/1.93  tff(c_3448, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_30, c_3438])).
% 5.14/1.93  tff(c_3452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3191, c_3448])).
% 5.14/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/1.93  
% 5.14/1.93  Inference rules
% 5.14/1.93  ----------------------
% 5.14/1.93  #Ref     : 0
% 5.14/1.93  #Sup     : 738
% 5.14/1.93  #Fact    : 0
% 5.14/1.93  #Define  : 0
% 5.14/1.93  #Split   : 9
% 5.14/1.93  #Chain   : 0
% 5.14/1.93  #Close   : 0
% 5.14/1.93  
% 5.14/1.93  Ordering : KBO
% 5.14/1.93  
% 5.14/1.93  Simplification rules
% 5.14/1.93  ----------------------
% 5.14/1.93  #Subsume      : 192
% 5.14/1.93  #Demod        : 112
% 5.14/1.93  #Tautology    : 163
% 5.14/1.93  #SimpNegUnit  : 191
% 5.14/1.93  #BackRed      : 0
% 5.14/1.93  
% 5.14/1.93  #Partial instantiations: 0
% 5.14/1.93  #Strategies tried      : 1
% 5.14/1.93  
% 5.14/1.93  Timing (in seconds)
% 5.14/1.93  ----------------------
% 5.14/1.94  Preprocessing        : 0.34
% 5.14/1.94  Parsing              : 0.18
% 5.14/1.94  CNF conversion       : 0.03
% 5.14/1.94  Main loop            : 0.81
% 5.14/1.94  Inferencing          : 0.31
% 5.14/1.94  Reduction            : 0.23
% 5.14/1.94  Demodulation         : 0.13
% 5.14/1.94  BG Simplification    : 0.04
% 5.14/1.94  Subsumption          : 0.18
% 5.14/1.94  Abstraction          : 0.04
% 5.14/1.94  MUC search           : 0.00
% 5.14/1.94  Cooper               : 0.00
% 5.14/1.94  Total                : 1.20
% 5.14/1.94  Index Insertion      : 0.00
% 5.14/1.94  Index Deletion       : 0.00
% 5.14/1.94  Index Matching       : 0.00
% 5.14/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
