%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:51 EST 2020

% Result     : Theorem 6.70s
% Output     : CNFRefutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 607 expanded)
%              Number of leaves         :   44 ( 229 expanded)
%              Depth                    :   15
%              Number of atoms          :  390 (2352 expanded)
%              Number of equality atoms :   17 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_198,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_137,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_178,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_166,axiom,(
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

tff(f_110,axiom,(
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

tff(f_72,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(c_22,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_126,plain,(
    ! [A_64,B_65] :
      ( ~ r2_hidden('#skF_2'(A_64,B_65),B_65)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_131,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_68,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_77,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_78,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_74])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_99,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_99])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_164,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75),B_76)
      | ~ r1_tarski(A_75,B_76)
      | v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_4,c_132])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_425,plain,(
    ! [A_115,B_116,B_117] :
      ( r2_hidden('#skF_1'(A_115),B_116)
      | ~ r1_tarski(B_117,B_116)
      | ~ r1_tarski(A_115,B_117)
      | v1_xboole_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_164,c_6])).

tff(c_450,plain,(
    ! [A_118] :
      ( r2_hidden('#skF_1'(A_118),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_118,'#skF_5')
      | v1_xboole_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_108,c_425])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_460,plain,(
    ! [A_118] :
      ( m1_subset_1('#skF_1'(A_118),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_118,'#skF_5')
      | v1_xboole_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_450,c_14])).

tff(c_174,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1('#skF_1'(A_75),B_76)
      | ~ r1_tarski(A_75,B_76)
      | v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_164,c_14])).

tff(c_12,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(A_50,B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_147,plain,(
    ! [A_73,B_74] :
      ( k6_domain_1(A_73,B_74) = k1_tarski(B_74)
      | ~ m1_subset_1(B_74,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_162,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = k1_tarski('#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_97,c_147])).

tff(c_214,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1(k6_domain_1(A_82,B_83),k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_83,A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_227,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k6_domain_1(A_85,B_86),A_85)
      | ~ m1_subset_1(B_86,A_85)
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_214,c_16])).

tff(c_546,plain,(
    ! [A_129] :
      ( r1_tarski(k1_tarski('#skF_1'(A_129)),A_129)
      | ~ m1_subset_1('#skF_1'(A_129),A_129)
      | v1_xboole_0(A_129)
      | v1_xboole_0(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_227])).

tff(c_42,plain,(
    ! [B_32,A_30] :
      ( B_32 = A_30
      | ~ r1_tarski(A_30,B_32)
      | ~ v1_zfmisc_1(B_32)
      | v1_xboole_0(B_32)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_560,plain,(
    ! [A_129] :
      ( k1_tarski('#skF_1'(A_129)) = A_129
      | ~ v1_zfmisc_1(A_129)
      | v1_xboole_0(k1_tarski('#skF_1'(A_129)))
      | ~ m1_subset_1('#skF_1'(A_129),A_129)
      | v1_xboole_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_546,c_42])).

tff(c_616,plain,(
    ! [A_132] :
      ( k1_tarski('#skF_1'(A_132)) = A_132
      | ~ v1_zfmisc_1(A_132)
      | ~ m1_subset_1('#skF_1'(A_132),A_132)
      | v1_xboole_0(A_132) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_560])).

tff(c_624,plain,(
    ! [B_76] :
      ( k1_tarski('#skF_1'(B_76)) = B_76
      | ~ v1_zfmisc_1(B_76)
      | ~ r1_tarski(B_76,B_76)
      | v1_xboole_0(B_76) ) ),
    inference(resolution,[status(thm)],[c_174,c_616])).

tff(c_636,plain,(
    ! [B_76] :
      ( k1_tarski('#skF_1'(B_76)) = B_76
      | ~ v1_zfmisc_1(B_76)
      | v1_xboole_0(B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_624])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    ! [B_77,A_78] :
      ( ~ v1_xboole_0(B_77)
      | ~ r1_tarski(A_78,B_77)
      | v1_xboole_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_164,c_2])).

tff(c_188,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_176])).

tff(c_194,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_188])).

tff(c_462,plain,(
    ! [A_119] :
      ( m1_subset_1('#skF_1'(A_119),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_119,'#skF_5')
      | v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_450,c_14])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( k6_domain_1(A_23,B_24) = k1_tarski(B_24)
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_465,plain,(
    ! [A_119] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_119)) = k1_tarski('#skF_1'(A_119))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_119,'#skF_5')
      | v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_462,c_30])).

tff(c_654,plain,(
    ! [A_134] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_134)) = k1_tarski('#skF_1'(A_134))
      | ~ r1_tarski(A_134,'#skF_5')
      | v1_xboole_0(A_134) ) ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_465])).

tff(c_54,plain,(
    ! [A_39,B_41] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_39),B_41),A_39)
      | ~ m1_subset_1(B_41,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_660,plain,(
    ! [A_134] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_134)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_134),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_134,'#skF_5')
      | v1_xboole_0(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_54])).

tff(c_680,plain,(
    ! [A_134] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_134)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_134),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_134,'#skF_5')
      | v1_xboole_0(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_660])).

tff(c_881,plain,(
    ! [A_153] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_153)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_153),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_153,'#skF_5')
      | v1_xboole_0(A_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_680])).

tff(c_4728,plain,(
    ! [B_335] :
      ( v2_tex_2(B_335,'#skF_4')
      | ~ m1_subset_1('#skF_1'(B_335),u1_struct_0('#skF_4'))
      | ~ r1_tarski(B_335,'#skF_5')
      | v1_xboole_0(B_335)
      | ~ v1_zfmisc_1(B_335)
      | v1_xboole_0(B_335) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_881])).

tff(c_4811,plain,(
    ! [A_336] :
      ( v2_tex_2(A_336,'#skF_4')
      | ~ v1_zfmisc_1(A_336)
      | ~ r1_tarski(A_336,'#skF_5')
      | v1_xboole_0(A_336) ) ),
    inference(resolution,[status(thm)],[c_460,c_4728])).

tff(c_4814,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4811,c_77])).

tff(c_4817,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_4814])).

tff(c_4819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4817])).

tff(c_4821,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_5669,plain,(
    ! [A_449,B_450] :
      ( ~ v2_struct_0('#skF_3'(A_449,B_450))
      | ~ v2_tex_2(B_450,A_449)
      | ~ m1_subset_1(B_450,k1_zfmisc_1(u1_struct_0(A_449)))
      | v1_xboole_0(B_450)
      | ~ l1_pre_topc(A_449)
      | ~ v2_pre_topc(A_449)
      | v2_struct_0(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_5696,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_5669])).

tff(c_5705,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_4821,c_5696])).

tff(c_5706,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_5705])).

tff(c_5470,plain,(
    ! [A_433,B_434] :
      ( v1_tdlat_3('#skF_3'(A_433,B_434))
      | ~ v2_tex_2(B_434,A_433)
      | ~ m1_subset_1(B_434,k1_zfmisc_1(u1_struct_0(A_433)))
      | v1_xboole_0(B_434)
      | ~ l1_pre_topc(A_433)
      | ~ v2_pre_topc(A_433)
      | v2_struct_0(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_5497,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_5470])).

tff(c_5506,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_4821,c_5497])).

tff(c_5507,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_5506])).

tff(c_36,plain,(
    ! [A_26] :
      ( v7_struct_0(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v1_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4820,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6155,plain,(
    ! [A_475,B_476] :
      ( u1_struct_0('#skF_3'(A_475,B_476)) = B_476
      | ~ v2_tex_2(B_476,A_475)
      | ~ m1_subset_1(B_476,k1_zfmisc_1(u1_struct_0(A_475)))
      | v1_xboole_0(B_476)
      | ~ l1_pre_topc(A_475)
      | ~ v2_pre_topc(A_475)
      | v2_struct_0(A_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_6194,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6155])).

tff(c_6208,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_4821,c_6194])).

tff(c_6209,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_6208])).

tff(c_26,plain,(
    ! [A_20] :
      ( v1_zfmisc_1(u1_struct_0(A_20))
      | ~ l1_struct_0(A_20)
      | ~ v7_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6228,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6209,c_26])).

tff(c_6237,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_4820,c_6228])).

tff(c_6239,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6237])).

tff(c_6242,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_6239])).

tff(c_6248,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5507,c_6242])).

tff(c_6249,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_5706,c_6248])).

tff(c_6251,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6249])).

tff(c_6324,plain,(
    ! [A_483,B_484] :
      ( m1_pre_topc('#skF_3'(A_483,B_484),A_483)
      | ~ v2_tex_2(B_484,A_483)
      | ~ m1_subset_1(B_484,k1_zfmisc_1(u1_struct_0(A_483)))
      | v1_xboole_0(B_484)
      | ~ l1_pre_topc(A_483)
      | ~ v2_pre_topc(A_483)
      | v2_struct_0(A_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_6355,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6324])).

tff(c_6370,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_4821,c_6355])).

tff(c_6371,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_6370])).

tff(c_24,plain,(
    ! [B_19,A_17] :
      ( l1_pre_topc(B_19)
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6377,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6371,c_24])).

tff(c_6384,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6377])).

tff(c_6386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6251,c_6384])).

tff(c_6387,plain,
    ( ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6249])).

tff(c_6389,plain,(
    ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6387])).

tff(c_62,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_6489,plain,(
    ! [A_492,B_493] :
      ( m1_pre_topc('#skF_3'(A_492,B_493),A_492)
      | ~ v2_tex_2(B_493,A_492)
      | ~ m1_subset_1(B_493,k1_zfmisc_1(u1_struct_0(A_492)))
      | v1_xboole_0(B_493)
      | ~ l1_pre_topc(A_492)
      | ~ v2_pre_topc(A_492)
      | v2_struct_0(A_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_6520,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6489])).

tff(c_6537,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_4821,c_6520])).

tff(c_6538,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_6537])).

tff(c_40,plain,(
    ! [B_29,A_27] :
      ( v2_tdlat_3(B_29)
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_tdlat_3(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6541,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6538,c_40])).

tff(c_6547,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_6541])).

tff(c_6549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6389,c_6547])).

tff(c_6550,plain,(
    ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6387])).

tff(c_6388,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6249])).

tff(c_6551,plain,(
    v2_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6387])).

tff(c_32,plain,(
    ! [A_25] :
      ( v2_pre_topc(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6554,plain,
    ( v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6551,c_32])).

tff(c_6557,plain,(
    v2_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6388,c_6554])).

tff(c_6585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6550,c_6557])).

tff(c_6586,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6237])).

tff(c_6591,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_22,c_6586])).

tff(c_6592,plain,(
    ! [A_495,B_496] :
      ( m1_pre_topc('#skF_3'(A_495,B_496),A_495)
      | ~ v2_tex_2(B_496,A_495)
      | ~ m1_subset_1(B_496,k1_zfmisc_1(u1_struct_0(A_495)))
      | v1_xboole_0(B_496)
      | ~ l1_pre_topc(A_495)
      | ~ v2_pre_topc(A_495)
      | v2_struct_0(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_6623,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6592])).

tff(c_6638,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_4821,c_6623])).

tff(c_6639,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_6638])).

tff(c_6645,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6639,c_24])).

tff(c_6652,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6645])).

tff(c_6654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6591,c_6652])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.70/2.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.51  
% 6.70/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.51  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 6.70/2.51  
% 6.70/2.51  %Foreground sorts:
% 6.70/2.51  
% 6.70/2.51  
% 6.70/2.51  %Background operators:
% 6.70/2.51  
% 6.70/2.51  
% 6.70/2.51  %Foreground operators:
% 6.70/2.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.70/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.70/2.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.70/2.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.70/2.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.70/2.51  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 6.70/2.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.70/2.51  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 6.70/2.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.70/2.51  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.70/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.70/2.51  tff('#skF_5', type, '#skF_5': $i).
% 6.70/2.51  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.70/2.51  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.70/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.70/2.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.70/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.70/2.51  tff('#skF_4', type, '#skF_4': $i).
% 6.70/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.70/2.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.70/2.51  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 6.70/2.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.70/2.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.70/2.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.70/2.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.70/2.51  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 6.70/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.70/2.51  
% 7.01/2.53  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.01/2.53  tff(f_198, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 7.01/2.53  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.01/2.53  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.01/2.53  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.01/2.53  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 7.01/2.54  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 7.01/2.54  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 7.01/2.54  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 7.01/2.54  tff(f_137, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 7.01/2.54  tff(f_178, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 7.01/2.54  tff(f_166, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 7.01/2.54  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_1)).
% 7.01/2.54  tff(f_72, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 7.01/2.54  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.01/2.54  tff(f_124, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 7.01/2.54  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 7.01/2.54  tff(c_22, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.01/2.54  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.01/2.54  tff(c_58, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.01/2.54  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.01/2.54  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.01/2.54  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.01/2.54  tff(c_126, plain, (![A_64, B_65]: (~r2_hidden('#skF_2'(A_64, B_65), B_65) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.01/2.54  tff(c_131, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_126])).
% 7.01/2.54  tff(c_68, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.01/2.54  tff(c_77, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 7.01/2.54  tff(c_74, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.01/2.54  tff(c_78, plain, (v1_zfmisc_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_77, c_74])).
% 7.01/2.54  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.01/2.54  tff(c_99, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.01/2.54  tff(c_108, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_99])).
% 7.01/2.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.01/2.54  tff(c_132, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.01/2.54  tff(c_164, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75), B_76) | ~r1_tarski(A_75, B_76) | v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_4, c_132])).
% 7.01/2.54  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.01/2.54  tff(c_425, plain, (![A_115, B_116, B_117]: (r2_hidden('#skF_1'(A_115), B_116) | ~r1_tarski(B_117, B_116) | ~r1_tarski(A_115, B_117) | v1_xboole_0(A_115))), inference(resolution, [status(thm)], [c_164, c_6])).
% 7.01/2.54  tff(c_450, plain, (![A_118]: (r2_hidden('#skF_1'(A_118), u1_struct_0('#skF_4')) | ~r1_tarski(A_118, '#skF_5') | v1_xboole_0(A_118))), inference(resolution, [status(thm)], [c_108, c_425])).
% 7.01/2.54  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.01/2.54  tff(c_460, plain, (![A_118]: (m1_subset_1('#skF_1'(A_118), u1_struct_0('#skF_4')) | ~r1_tarski(A_118, '#skF_5') | v1_xboole_0(A_118))), inference(resolution, [status(thm)], [c_450, c_14])).
% 7.01/2.54  tff(c_174, plain, (![A_75, B_76]: (m1_subset_1('#skF_1'(A_75), B_76) | ~r1_tarski(A_75, B_76) | v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_164, c_14])).
% 7.01/2.54  tff(c_12, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.01/2.54  tff(c_93, plain, (![A_50, B_51]: (m1_subset_1(A_50, B_51) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.01/2.54  tff(c_97, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_93])).
% 7.01/2.54  tff(c_147, plain, (![A_73, B_74]: (k6_domain_1(A_73, B_74)=k1_tarski(B_74) | ~m1_subset_1(B_74, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.01/2.54  tff(c_162, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=k1_tarski('#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_97, c_147])).
% 7.01/2.54  tff(c_214, plain, (![A_82, B_83]: (m1_subset_1(k6_domain_1(A_82, B_83), k1_zfmisc_1(A_82)) | ~m1_subset_1(B_83, A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.01/2.54  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.01/2.54  tff(c_227, plain, (![A_85, B_86]: (r1_tarski(k6_domain_1(A_85, B_86), A_85) | ~m1_subset_1(B_86, A_85) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_214, c_16])).
% 7.01/2.54  tff(c_546, plain, (![A_129]: (r1_tarski(k1_tarski('#skF_1'(A_129)), A_129) | ~m1_subset_1('#skF_1'(A_129), A_129) | v1_xboole_0(A_129) | v1_xboole_0(A_129))), inference(superposition, [status(thm), theory('equality')], [c_162, c_227])).
% 7.01/2.54  tff(c_42, plain, (![B_32, A_30]: (B_32=A_30 | ~r1_tarski(A_30, B_32) | ~v1_zfmisc_1(B_32) | v1_xboole_0(B_32) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.01/2.54  tff(c_560, plain, (![A_129]: (k1_tarski('#skF_1'(A_129))=A_129 | ~v1_zfmisc_1(A_129) | v1_xboole_0(k1_tarski('#skF_1'(A_129))) | ~m1_subset_1('#skF_1'(A_129), A_129) | v1_xboole_0(A_129))), inference(resolution, [status(thm)], [c_546, c_42])).
% 7.01/2.54  tff(c_616, plain, (![A_132]: (k1_tarski('#skF_1'(A_132))=A_132 | ~v1_zfmisc_1(A_132) | ~m1_subset_1('#skF_1'(A_132), A_132) | v1_xboole_0(A_132))), inference(negUnitSimplification, [status(thm)], [c_12, c_560])).
% 7.01/2.54  tff(c_624, plain, (![B_76]: (k1_tarski('#skF_1'(B_76))=B_76 | ~v1_zfmisc_1(B_76) | ~r1_tarski(B_76, B_76) | v1_xboole_0(B_76))), inference(resolution, [status(thm)], [c_174, c_616])).
% 7.01/2.54  tff(c_636, plain, (![B_76]: (k1_tarski('#skF_1'(B_76))=B_76 | ~v1_zfmisc_1(B_76) | v1_xboole_0(B_76))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_624])).
% 7.01/2.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.01/2.54  tff(c_176, plain, (![B_77, A_78]: (~v1_xboole_0(B_77) | ~r1_tarski(A_78, B_77) | v1_xboole_0(A_78))), inference(resolution, [status(thm)], [c_164, c_2])).
% 7.01/2.54  tff(c_188, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_108, c_176])).
% 7.01/2.54  tff(c_194, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_188])).
% 7.01/2.54  tff(c_462, plain, (![A_119]: (m1_subset_1('#skF_1'(A_119), u1_struct_0('#skF_4')) | ~r1_tarski(A_119, '#skF_5') | v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_450, c_14])).
% 7.01/2.54  tff(c_30, plain, (![A_23, B_24]: (k6_domain_1(A_23, B_24)=k1_tarski(B_24) | ~m1_subset_1(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.01/2.54  tff(c_465, plain, (![A_119]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_119))=k1_tarski('#skF_1'(A_119)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(A_119, '#skF_5') | v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_462, c_30])).
% 7.01/2.54  tff(c_654, plain, (![A_134]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_134))=k1_tarski('#skF_1'(A_134)) | ~r1_tarski(A_134, '#skF_5') | v1_xboole_0(A_134))), inference(negUnitSimplification, [status(thm)], [c_194, c_465])).
% 7.01/2.54  tff(c_54, plain, (![A_39, B_41]: (v2_tex_2(k6_domain_1(u1_struct_0(A_39), B_41), A_39) | ~m1_subset_1(B_41, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_178])).
% 7.01/2.54  tff(c_660, plain, (![A_134]: (v2_tex_2(k1_tarski('#skF_1'(A_134)), '#skF_4') | ~m1_subset_1('#skF_1'(A_134), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_134, '#skF_5') | v1_xboole_0(A_134))), inference(superposition, [status(thm), theory('equality')], [c_654, c_54])).
% 7.01/2.54  tff(c_680, plain, (![A_134]: (v2_tex_2(k1_tarski('#skF_1'(A_134)), '#skF_4') | ~m1_subset_1('#skF_1'(A_134), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r1_tarski(A_134, '#skF_5') | v1_xboole_0(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_660])).
% 7.01/2.54  tff(c_881, plain, (![A_153]: (v2_tex_2(k1_tarski('#skF_1'(A_153)), '#skF_4') | ~m1_subset_1('#skF_1'(A_153), u1_struct_0('#skF_4')) | ~r1_tarski(A_153, '#skF_5') | v1_xboole_0(A_153))), inference(negUnitSimplification, [status(thm)], [c_66, c_680])).
% 7.01/2.54  tff(c_4728, plain, (![B_335]: (v2_tex_2(B_335, '#skF_4') | ~m1_subset_1('#skF_1'(B_335), u1_struct_0('#skF_4')) | ~r1_tarski(B_335, '#skF_5') | v1_xboole_0(B_335) | ~v1_zfmisc_1(B_335) | v1_xboole_0(B_335))), inference(superposition, [status(thm), theory('equality')], [c_636, c_881])).
% 7.01/2.54  tff(c_4811, plain, (![A_336]: (v2_tex_2(A_336, '#skF_4') | ~v1_zfmisc_1(A_336) | ~r1_tarski(A_336, '#skF_5') | v1_xboole_0(A_336))), inference(resolution, [status(thm)], [c_460, c_4728])).
% 7.01/2.54  tff(c_4814, plain, (~v1_zfmisc_1('#skF_5') | ~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4811, c_77])).
% 7.01/2.54  tff(c_4817, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_4814])).
% 7.01/2.54  tff(c_4819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_4817])).
% 7.01/2.54  tff(c_4821, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 7.01/2.54  tff(c_5669, plain, (![A_449, B_450]: (~v2_struct_0('#skF_3'(A_449, B_450)) | ~v2_tex_2(B_450, A_449) | ~m1_subset_1(B_450, k1_zfmisc_1(u1_struct_0(A_449))) | v1_xboole_0(B_450) | ~l1_pre_topc(A_449) | ~v2_pre_topc(A_449) | v2_struct_0(A_449))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.01/2.54  tff(c_5696, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_5669])).
% 7.01/2.54  tff(c_5705, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_4821, c_5696])).
% 7.01/2.54  tff(c_5706, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_5705])).
% 7.01/2.54  tff(c_5470, plain, (![A_433, B_434]: (v1_tdlat_3('#skF_3'(A_433, B_434)) | ~v2_tex_2(B_434, A_433) | ~m1_subset_1(B_434, k1_zfmisc_1(u1_struct_0(A_433))) | v1_xboole_0(B_434) | ~l1_pre_topc(A_433) | ~v2_pre_topc(A_433) | v2_struct_0(A_433))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.01/2.54  tff(c_5497, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_5470])).
% 7.01/2.54  tff(c_5506, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_4821, c_5497])).
% 7.01/2.54  tff(c_5507, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_5506])).
% 7.01/2.54  tff(c_36, plain, (![A_26]: (v7_struct_0(A_26) | ~v2_tdlat_3(A_26) | ~v1_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.01/2.54  tff(c_4820, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_68])).
% 7.01/2.54  tff(c_6155, plain, (![A_475, B_476]: (u1_struct_0('#skF_3'(A_475, B_476))=B_476 | ~v2_tex_2(B_476, A_475) | ~m1_subset_1(B_476, k1_zfmisc_1(u1_struct_0(A_475))) | v1_xboole_0(B_476) | ~l1_pre_topc(A_475) | ~v2_pre_topc(A_475) | v2_struct_0(A_475))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.01/2.54  tff(c_6194, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_6155])).
% 7.01/2.54  tff(c_6208, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_4821, c_6194])).
% 7.01/2.54  tff(c_6209, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_6208])).
% 7.01/2.54  tff(c_26, plain, (![A_20]: (v1_zfmisc_1(u1_struct_0(A_20)) | ~l1_struct_0(A_20) | ~v7_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.01/2.54  tff(c_6228, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6209, c_26])).
% 7.01/2.54  tff(c_6237, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_4820, c_6228])).
% 7.01/2.54  tff(c_6239, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_6237])).
% 7.01/2.54  tff(c_6242, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_6239])).
% 7.01/2.54  tff(c_6248, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5507, c_6242])).
% 7.01/2.54  tff(c_6249, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_5706, c_6248])).
% 7.01/2.54  tff(c_6251, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_6249])).
% 7.01/2.54  tff(c_6324, plain, (![A_483, B_484]: (m1_pre_topc('#skF_3'(A_483, B_484), A_483) | ~v2_tex_2(B_484, A_483) | ~m1_subset_1(B_484, k1_zfmisc_1(u1_struct_0(A_483))) | v1_xboole_0(B_484) | ~l1_pre_topc(A_483) | ~v2_pre_topc(A_483) | v2_struct_0(A_483))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.01/2.54  tff(c_6355, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_6324])).
% 7.01/2.54  tff(c_6370, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_4821, c_6355])).
% 7.01/2.54  tff(c_6371, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_6370])).
% 7.01/2.54  tff(c_24, plain, (![B_19, A_17]: (l1_pre_topc(B_19) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.01/2.54  tff(c_6377, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6371, c_24])).
% 7.01/2.54  tff(c_6384, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6377])).
% 7.01/2.54  tff(c_6386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6251, c_6384])).
% 7.01/2.54  tff(c_6387, plain, (~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_6249])).
% 7.01/2.54  tff(c_6389, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_6387])).
% 7.01/2.54  tff(c_62, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 7.01/2.54  tff(c_6489, plain, (![A_492, B_493]: (m1_pre_topc('#skF_3'(A_492, B_493), A_492) | ~v2_tex_2(B_493, A_492) | ~m1_subset_1(B_493, k1_zfmisc_1(u1_struct_0(A_492))) | v1_xboole_0(B_493) | ~l1_pre_topc(A_492) | ~v2_pre_topc(A_492) | v2_struct_0(A_492))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.01/2.54  tff(c_6520, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_6489])).
% 7.01/2.54  tff(c_6537, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_4821, c_6520])).
% 7.01/2.54  tff(c_6538, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_6537])).
% 7.01/2.54  tff(c_40, plain, (![B_29, A_27]: (v2_tdlat_3(B_29) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27) | ~v2_tdlat_3(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.01/2.54  tff(c_6541, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_6538, c_40])).
% 7.01/2.54  tff(c_6547, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_6541])).
% 7.01/2.54  tff(c_6549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_6389, c_6547])).
% 7.01/2.54  tff(c_6550, plain, (~v2_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_6387])).
% 7.01/2.54  tff(c_6388, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_6249])).
% 7.01/2.54  tff(c_6551, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_6387])).
% 7.01/2.54  tff(c_32, plain, (![A_25]: (v2_pre_topc(A_25) | ~v2_tdlat_3(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.01/2.54  tff(c_6554, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_6551, c_32])).
% 7.01/2.54  tff(c_6557, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6388, c_6554])).
% 7.01/2.54  tff(c_6585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6550, c_6557])).
% 7.01/2.54  tff(c_6586, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_6237])).
% 7.01/2.54  tff(c_6591, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_6586])).
% 7.01/2.54  tff(c_6592, plain, (![A_495, B_496]: (m1_pre_topc('#skF_3'(A_495, B_496), A_495) | ~v2_tex_2(B_496, A_495) | ~m1_subset_1(B_496, k1_zfmisc_1(u1_struct_0(A_495))) | v1_xboole_0(B_496) | ~l1_pre_topc(A_495) | ~v2_pre_topc(A_495) | v2_struct_0(A_495))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.01/2.54  tff(c_6623, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_6592])).
% 7.01/2.54  tff(c_6638, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_4821, c_6623])).
% 7.01/2.54  tff(c_6639, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_6638])).
% 7.01/2.54  tff(c_6645, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6639, c_24])).
% 7.01/2.54  tff(c_6652, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6645])).
% 7.01/2.54  tff(c_6654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6591, c_6652])).
% 7.01/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/2.54  
% 7.01/2.54  Inference rules
% 7.01/2.54  ----------------------
% 7.01/2.54  #Ref     : 0
% 7.01/2.54  #Sup     : 1484
% 7.01/2.54  #Fact    : 0
% 7.01/2.54  #Define  : 0
% 7.01/2.54  #Split   : 14
% 7.01/2.54  #Chain   : 0
% 7.01/2.54  #Close   : 0
% 7.01/2.54  
% 7.01/2.54  Ordering : KBO
% 7.01/2.54  
% 7.01/2.54  Simplification rules
% 7.01/2.54  ----------------------
% 7.01/2.54  #Subsume      : 336
% 7.01/2.54  #Demod        : 163
% 7.01/2.54  #Tautology    : 164
% 7.01/2.54  #SimpNegUnit  : 201
% 7.01/2.54  #BackRed      : 0
% 7.01/2.54  
% 7.01/2.54  #Partial instantiations: 0
% 7.01/2.54  #Strategies tried      : 1
% 7.01/2.54  
% 7.01/2.54  Timing (in seconds)
% 7.01/2.54  ----------------------
% 7.01/2.54  Preprocessing        : 0.35
% 7.01/2.54  Parsing              : 0.19
% 7.01/2.54  CNF conversion       : 0.02
% 7.01/2.54  Main loop            : 1.35
% 7.01/2.54  Inferencing          : 0.45
% 7.01/2.54  Reduction            : 0.35
% 7.01/2.54  Demodulation         : 0.20
% 7.01/2.54  BG Simplification    : 0.05
% 7.01/2.54  Subsumption          : 0.39
% 7.01/2.54  Abstraction          : 0.07
% 7.01/2.54  MUC search           : 0.00
% 7.01/2.54  Cooper               : 0.00
% 7.01/2.54  Total                : 1.75
% 7.01/2.54  Index Insertion      : 0.00
% 7.01/2.54  Index Deletion       : 0.00
% 7.01/2.54  Index Matching       : 0.00
% 7.01/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
