%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:29 EST 2020

% Result     : Theorem 7.70s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 422 expanded)
%              Number of leaves         :   30 ( 158 expanded)
%              Depth                    :   17
%              Number of atoms          :  156 ( 873 expanded)
%              Number of equality atoms :   31 ( 172 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_292,plain,(
    ! [A_88,B_89] :
      ( r1_tarski('#skF_2'(A_88,B_89),B_89)
      | v2_tex_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_300,plain,
    ( r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_292])).

tff(c_305,plain,
    ( r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_300])).

tff(c_306,plain,(
    r1_tarski('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_305])).

tff(c_38,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_55,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_46])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_10])).

tff(c_322,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_306,c_71])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_178,plain,(
    ! [B_74,A_75] :
      ( v4_pre_topc(B_74,A_75)
      | ~ v1_xboole_0(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_192,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_178])).

tff(c_200,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_192])).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_57,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_8])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_118,plain,(
    ! [A_64,B_65,C_66] :
      ( k9_subset_1(A_64,B_65,C_66) = k3_xboole_0(B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_228,plain,(
    ! [B_80,B_81,A_82] :
      ( k9_subset_1(B_80,B_81,A_82) = k3_xboole_0(B_81,A_82)
      | ~ r1_tarski(A_82,B_80) ) ),
    inference(resolution,[status(thm)],[c_18,c_118])).

tff(c_239,plain,(
    ! [A_83,B_84] : k9_subset_1(A_83,B_84,'#skF_4') = k3_xboole_0(B_84,'#skF_4') ),
    inference(resolution,[status(thm)],[c_57,c_228])).

tff(c_100,plain,(
    ! [A_58,B_59,C_60] :
      ( m1_subset_1(k9_subset_1(A_58,B_59,C_60),k1_zfmisc_1(A_58))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_105,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(k9_subset_1(A_61,B_62,C_63),A_61)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61)) ) ),
    inference(resolution,[status(thm)],[c_100,c_16])).

tff(c_160,plain,(
    ! [B_70,C_71] :
      ( k9_subset_1('#skF_4',B_70,C_71) = '#skF_4'
      | ~ m1_subset_1(C_71,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_105,c_71])).

tff(c_169,plain,(
    ! [B_72,A_73] :
      ( k9_subset_1('#skF_4',B_72,A_73) = '#skF_4'
      | ~ r1_tarski(A_73,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_160])).

tff(c_177,plain,(
    ! [B_72] : k9_subset_1('#skF_4',B_72,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_57,c_169])).

tff(c_245,plain,(
    ! [B_84] : k3_xboole_0(B_84,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_177])).

tff(c_237,plain,(
    ! [A_5,B_81] : k9_subset_1(A_5,B_81,'#skF_4') = k3_xboole_0(B_81,'#skF_4') ),
    inference(resolution,[status(thm)],[c_57,c_228])).

tff(c_260,plain,(
    ! [A_5,B_81] : k9_subset_1(A_5,B_81,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_237])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k9_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_933,plain,(
    ! [A_149,B_150,B_151,C_152] :
      ( k9_subset_1(A_149,B_150,k9_subset_1(A_149,B_151,C_152)) = k3_xboole_0(B_150,k9_subset_1(A_149,B_151,C_152))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(A_149)) ) ),
    inference(resolution,[status(thm)],[c_12,c_118])).

tff(c_954,plain,(
    ! [B_153,B_154,B_155,A_156] :
      ( k9_subset_1(B_153,B_154,k9_subset_1(B_153,B_155,A_156)) = k3_xboole_0(B_154,k9_subset_1(B_153,B_155,A_156))
      | ~ r1_tarski(A_156,B_153) ) ),
    inference(resolution,[status(thm)],[c_18,c_933])).

tff(c_382,plain,(
    ! [B_95,B_96,C_97] :
      ( k9_subset_1('#skF_4',B_95,k9_subset_1('#skF_4',B_96,C_97)) = '#skF_4'
      | ~ m1_subset_1(C_97,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_160])).

tff(c_390,plain,(
    ! [B_95,B_96,A_13] :
      ( k9_subset_1('#skF_4',B_95,k9_subset_1('#skF_4',B_96,A_13)) = '#skF_4'
      | ~ r1_tarski(A_13,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_382])).

tff(c_993,plain,(
    ! [B_154,B_155,A_156] :
      ( k3_xboole_0(B_154,k9_subset_1('#skF_4',B_155,A_156)) = '#skF_4'
      | ~ r1_tarski(A_156,'#skF_4')
      | ~ r1_tarski(A_156,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_390])).

tff(c_90,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(A_53,C_54)
      | ~ r1_tarski(B_55,C_54)
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_93,plain,(
    ! [A_53,A_5] :
      ( r1_tarski(A_53,A_5)
      | ~ r1_tarski(A_53,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_57,c_90])).

tff(c_334,plain,(
    ! [B_90,C_91,A_92] :
      ( r1_tarski(k9_subset_1('#skF_4',B_90,C_91),A_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_105,c_93])).

tff(c_126,plain,(
    ! [B_14,B_65,A_13] :
      ( k9_subset_1(B_14,B_65,A_13) = k3_xboole_0(B_65,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_118])).

tff(c_1260,plain,(
    ! [A_170,B_171,B_172,C_173] :
      ( k9_subset_1(A_170,B_171,k9_subset_1('#skF_4',B_172,C_173)) = k3_xboole_0(B_171,k9_subset_1('#skF_4',B_172,C_173))
      | ~ m1_subset_1(C_173,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_334,c_126])).

tff(c_1273,plain,(
    ! [A_174,B_175,B_176,A_177] :
      ( k9_subset_1(A_174,B_175,k9_subset_1('#skF_4',B_176,A_177)) = k3_xboole_0(B_175,k9_subset_1('#skF_4',B_176,A_177))
      | ~ r1_tarski(A_177,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_1260])).

tff(c_2942,plain,(
    ! [B_271,B_272,A_273,A_274] :
      ( m1_subset_1(k3_xboole_0(B_271,k9_subset_1('#skF_4',B_272,A_273)),k1_zfmisc_1(A_274))
      | ~ m1_subset_1(k9_subset_1('#skF_4',B_272,A_273),k1_zfmisc_1(A_274))
      | ~ r1_tarski(A_273,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1273,c_12])).

tff(c_4493,plain,(
    ! [A_346,B_347,A_348] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(A_346))
      | ~ m1_subset_1(k9_subset_1('#skF_4',B_347,A_348),k1_zfmisc_1(A_346))
      | ~ r1_tarski(A_348,'#skF_4')
      | ~ r1_tarski(A_348,'#skF_4')
      | ~ r1_tarski(A_348,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_2942])).

tff(c_4541,plain,(
    ! [B_349,A_350,B_351] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(B_349))
      | ~ r1_tarski(A_350,'#skF_4')
      | ~ r1_tarski(k9_subset_1('#skF_4',B_351,A_350),B_349) ) ),
    inference(resolution,[status(thm)],[c_18,c_4493])).

tff(c_4578,plain,(
    ! [B_349] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(B_349))
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ r1_tarski('#skF_4',B_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_4541])).

tff(c_4597,plain,(
    ! [B_349] : m1_subset_1('#skF_4',k1_zfmisc_1(B_349)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_4578])).

tff(c_682,plain,(
    ! [A_127,B_128,D_129] :
      ( k9_subset_1(u1_struct_0(A_127),B_128,D_129) != '#skF_2'(A_127,B_128)
      | ~ v4_pre_topc(D_129,A_127)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(u1_struct_0(A_127)))
      | v2_tex_2(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_685,plain,(
    ! [A_127,B_81] :
      ( '#skF_2'(A_127,B_81) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_127)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_127)))
      | v2_tex_2(B_81,A_127)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_682])).

tff(c_7712,plain,(
    ! [A_468,B_469] :
      ( '#skF_2'(A_468,B_469) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_468)
      | v2_tex_2(B_469,A_468)
      | ~ m1_subset_1(B_469,k1_zfmisc_1(u1_struct_0(A_468)))
      | ~ l1_pre_topc(A_468) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4597,c_685])).

tff(c_7751,plain,(
    ! [A_470] :
      ( '#skF_2'(A_470,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_470)
      | v2_tex_2('#skF_4',A_470)
      | ~ l1_pre_topc(A_470) ) ),
    inference(resolution,[status(thm)],[c_4597,c_7712])).

tff(c_7757,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_200,c_7751])).

tff(c_7761,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_322,c_7757])).

tff(c_7763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_7761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:25:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.70/2.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/2.75  
% 7.70/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/2.75  %$ v4_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 7.70/2.75  
% 7.70/2.75  %Foreground sorts:
% 7.70/2.75  
% 7.70/2.75  
% 7.70/2.75  %Background operators:
% 7.70/2.75  
% 7.70/2.75  
% 7.70/2.75  %Foreground operators:
% 7.70/2.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.70/2.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.70/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.70/2.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.70/2.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.70/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.70/2.75  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.70/2.75  tff('#skF_3', type, '#skF_3': $i).
% 7.70/2.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.70/2.75  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.70/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.70/2.75  tff('#skF_4', type, '#skF_4': $i).
% 7.70/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.70/2.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.70/2.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.70/2.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.70/2.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.70/2.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.70/2.75  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.70/2.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.70/2.75  
% 7.85/2.76  tff(f_101, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 7.85/2.76  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 7.85/2.76  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.85/2.76  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.85/2.76  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 7.85/2.76  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.85/2.76  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.85/2.76  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.85/2.76  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 7.85/2.76  tff(f_36, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.85/2.76  tff(c_34, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.85/2.76  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.85/2.76  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.85/2.76  tff(c_292, plain, (![A_88, B_89]: (r1_tarski('#skF_2'(A_88, B_89), B_89) | v2_tex_2(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.85/2.76  tff(c_300, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_292])).
% 7.85/2.76  tff(c_305, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_300])).
% 7.85/2.76  tff(c_306, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_305])).
% 7.85/2.76  tff(c_38, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.85/2.76  tff(c_46, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.85/2.76  tff(c_55, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_46])).
% 7.85/2.76  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.85/2.76  tff(c_71, plain, (![A_6]: (A_6='#skF_4' | ~r1_tarski(A_6, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_10])).
% 7.85/2.76  tff(c_322, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_306, c_71])).
% 7.85/2.76  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.85/2.76  tff(c_178, plain, (![B_74, A_75]: (v4_pre_topc(B_74, A_75) | ~v1_xboole_0(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.85/2.76  tff(c_192, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_178])).
% 7.85/2.76  tff(c_200, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_192])).
% 7.85/2.76  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.85/2.76  tff(c_57, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_8])).
% 7.85/2.76  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.85/2.76  tff(c_118, plain, (![A_64, B_65, C_66]: (k9_subset_1(A_64, B_65, C_66)=k3_xboole_0(B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.85/2.76  tff(c_228, plain, (![B_80, B_81, A_82]: (k9_subset_1(B_80, B_81, A_82)=k3_xboole_0(B_81, A_82) | ~r1_tarski(A_82, B_80))), inference(resolution, [status(thm)], [c_18, c_118])).
% 7.85/2.76  tff(c_239, plain, (![A_83, B_84]: (k9_subset_1(A_83, B_84, '#skF_4')=k3_xboole_0(B_84, '#skF_4'))), inference(resolution, [status(thm)], [c_57, c_228])).
% 7.85/2.76  tff(c_100, plain, (![A_58, B_59, C_60]: (m1_subset_1(k9_subset_1(A_58, B_59, C_60), k1_zfmisc_1(A_58)) | ~m1_subset_1(C_60, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.85/2.76  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.85/2.76  tff(c_105, plain, (![A_61, B_62, C_63]: (r1_tarski(k9_subset_1(A_61, B_62, C_63), A_61) | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)))), inference(resolution, [status(thm)], [c_100, c_16])).
% 7.85/2.76  tff(c_160, plain, (![B_70, C_71]: (k9_subset_1('#skF_4', B_70, C_71)='#skF_4' | ~m1_subset_1(C_71, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_105, c_71])).
% 7.85/2.76  tff(c_169, plain, (![B_72, A_73]: (k9_subset_1('#skF_4', B_72, A_73)='#skF_4' | ~r1_tarski(A_73, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_160])).
% 7.85/2.76  tff(c_177, plain, (![B_72]: (k9_subset_1('#skF_4', B_72, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_57, c_169])).
% 7.85/2.76  tff(c_245, plain, (![B_84]: (k3_xboole_0(B_84, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_239, c_177])).
% 7.85/2.76  tff(c_237, plain, (![A_5, B_81]: (k9_subset_1(A_5, B_81, '#skF_4')=k3_xboole_0(B_81, '#skF_4'))), inference(resolution, [status(thm)], [c_57, c_228])).
% 7.85/2.76  tff(c_260, plain, (![A_5, B_81]: (k9_subset_1(A_5, B_81, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_237])).
% 7.85/2.76  tff(c_12, plain, (![A_7, B_8, C_9]: (m1_subset_1(k9_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.85/2.76  tff(c_933, plain, (![A_149, B_150, B_151, C_152]: (k9_subset_1(A_149, B_150, k9_subset_1(A_149, B_151, C_152))=k3_xboole_0(B_150, k9_subset_1(A_149, B_151, C_152)) | ~m1_subset_1(C_152, k1_zfmisc_1(A_149)))), inference(resolution, [status(thm)], [c_12, c_118])).
% 7.85/2.76  tff(c_954, plain, (![B_153, B_154, B_155, A_156]: (k9_subset_1(B_153, B_154, k9_subset_1(B_153, B_155, A_156))=k3_xboole_0(B_154, k9_subset_1(B_153, B_155, A_156)) | ~r1_tarski(A_156, B_153))), inference(resolution, [status(thm)], [c_18, c_933])).
% 7.85/2.76  tff(c_382, plain, (![B_95, B_96, C_97]: (k9_subset_1('#skF_4', B_95, k9_subset_1('#skF_4', B_96, C_97))='#skF_4' | ~m1_subset_1(C_97, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_12, c_160])).
% 7.85/2.76  tff(c_390, plain, (![B_95, B_96, A_13]: (k9_subset_1('#skF_4', B_95, k9_subset_1('#skF_4', B_96, A_13))='#skF_4' | ~r1_tarski(A_13, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_382])).
% 7.85/2.76  tff(c_993, plain, (![B_154, B_155, A_156]: (k3_xboole_0(B_154, k9_subset_1('#skF_4', B_155, A_156))='#skF_4' | ~r1_tarski(A_156, '#skF_4') | ~r1_tarski(A_156, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_954, c_390])).
% 7.85/2.76  tff(c_90, plain, (![A_53, C_54, B_55]: (r1_tarski(A_53, C_54) | ~r1_tarski(B_55, C_54) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.85/2.76  tff(c_93, plain, (![A_53, A_5]: (r1_tarski(A_53, A_5) | ~r1_tarski(A_53, '#skF_4'))), inference(resolution, [status(thm)], [c_57, c_90])).
% 7.85/2.76  tff(c_334, plain, (![B_90, C_91, A_92]: (r1_tarski(k9_subset_1('#skF_4', B_90, C_91), A_92) | ~m1_subset_1(C_91, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_105, c_93])).
% 7.85/2.76  tff(c_126, plain, (![B_14, B_65, A_13]: (k9_subset_1(B_14, B_65, A_13)=k3_xboole_0(B_65, A_13) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_18, c_118])).
% 7.85/2.76  tff(c_1260, plain, (![A_170, B_171, B_172, C_173]: (k9_subset_1(A_170, B_171, k9_subset_1('#skF_4', B_172, C_173))=k3_xboole_0(B_171, k9_subset_1('#skF_4', B_172, C_173)) | ~m1_subset_1(C_173, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_334, c_126])).
% 7.85/2.76  tff(c_1273, plain, (![A_174, B_175, B_176, A_177]: (k9_subset_1(A_174, B_175, k9_subset_1('#skF_4', B_176, A_177))=k3_xboole_0(B_175, k9_subset_1('#skF_4', B_176, A_177)) | ~r1_tarski(A_177, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_1260])).
% 7.85/2.76  tff(c_2942, plain, (![B_271, B_272, A_273, A_274]: (m1_subset_1(k3_xboole_0(B_271, k9_subset_1('#skF_4', B_272, A_273)), k1_zfmisc_1(A_274)) | ~m1_subset_1(k9_subset_1('#skF_4', B_272, A_273), k1_zfmisc_1(A_274)) | ~r1_tarski(A_273, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1273, c_12])).
% 7.85/2.76  tff(c_4493, plain, (![A_346, B_347, A_348]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_346)) | ~m1_subset_1(k9_subset_1('#skF_4', B_347, A_348), k1_zfmisc_1(A_346)) | ~r1_tarski(A_348, '#skF_4') | ~r1_tarski(A_348, '#skF_4') | ~r1_tarski(A_348, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_993, c_2942])).
% 7.85/2.76  tff(c_4541, plain, (![B_349, A_350, B_351]: (m1_subset_1('#skF_4', k1_zfmisc_1(B_349)) | ~r1_tarski(A_350, '#skF_4') | ~r1_tarski(k9_subset_1('#skF_4', B_351, A_350), B_349))), inference(resolution, [status(thm)], [c_18, c_4493])).
% 7.85/2.76  tff(c_4578, plain, (![B_349]: (m1_subset_1('#skF_4', k1_zfmisc_1(B_349)) | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_4', B_349))), inference(superposition, [status(thm), theory('equality')], [c_260, c_4541])).
% 7.85/2.76  tff(c_4597, plain, (![B_349]: (m1_subset_1('#skF_4', k1_zfmisc_1(B_349)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_4578])).
% 7.85/2.76  tff(c_682, plain, (![A_127, B_128, D_129]: (k9_subset_1(u1_struct_0(A_127), B_128, D_129)!='#skF_2'(A_127, B_128) | ~v4_pre_topc(D_129, A_127) | ~m1_subset_1(D_129, k1_zfmisc_1(u1_struct_0(A_127))) | v2_tex_2(B_128, A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.85/2.76  tff(c_685, plain, (![A_127, B_81]: ('#skF_2'(A_127, B_81)!='#skF_4' | ~v4_pre_topc('#skF_4', A_127) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_127))) | v2_tex_2(B_81, A_127) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(superposition, [status(thm), theory('equality')], [c_260, c_682])).
% 7.85/2.76  tff(c_7712, plain, (![A_468, B_469]: ('#skF_2'(A_468, B_469)!='#skF_4' | ~v4_pre_topc('#skF_4', A_468) | v2_tex_2(B_469, A_468) | ~m1_subset_1(B_469, k1_zfmisc_1(u1_struct_0(A_468))) | ~l1_pre_topc(A_468))), inference(demodulation, [status(thm), theory('equality')], [c_4597, c_685])).
% 7.85/2.76  tff(c_7751, plain, (![A_470]: ('#skF_2'(A_470, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_470) | v2_tex_2('#skF_4', A_470) | ~l1_pre_topc(A_470))), inference(resolution, [status(thm)], [c_4597, c_7712])).
% 7.85/2.76  tff(c_7757, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_200, c_7751])).
% 7.85/2.76  tff(c_7761, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_322, c_7757])).
% 7.85/2.76  tff(c_7763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_7761])).
% 7.85/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/2.76  
% 7.85/2.76  Inference rules
% 7.85/2.76  ----------------------
% 7.85/2.76  #Ref     : 0
% 7.85/2.76  #Sup     : 1891
% 7.85/2.76  #Fact    : 0
% 7.85/2.76  #Define  : 0
% 7.85/2.76  #Split   : 2
% 7.85/2.76  #Chain   : 0
% 7.85/2.76  #Close   : 0
% 7.85/2.76  
% 7.85/2.76  Ordering : KBO
% 7.85/2.76  
% 7.85/2.76  Simplification rules
% 7.85/2.76  ----------------------
% 7.85/2.76  #Subsume      : 390
% 7.85/2.76  #Demod        : 1392
% 7.85/2.76  #Tautology    : 638
% 7.85/2.76  #SimpNegUnit  : 54
% 7.85/2.76  #BackRed      : 9
% 7.85/2.76  
% 7.85/2.76  #Partial instantiations: 0
% 7.85/2.76  #Strategies tried      : 1
% 7.85/2.76  
% 7.85/2.76  Timing (in seconds)
% 7.85/2.76  ----------------------
% 7.85/2.77  Preprocessing        : 0.31
% 7.85/2.77  Parsing              : 0.16
% 7.85/2.77  CNF conversion       : 0.02
% 7.85/2.77  Main loop            : 1.68
% 7.85/2.77  Inferencing          : 0.51
% 7.85/2.77  Reduction            : 0.49
% 7.85/2.77  Demodulation         : 0.35
% 7.85/2.77  BG Simplification    : 0.06
% 7.85/2.77  Subsumption          : 0.52
% 7.85/2.77  Abstraction          : 0.08
% 7.85/2.77  MUC search           : 0.00
% 7.85/2.77  Cooper               : 0.00
% 7.85/2.77  Total                : 2.03
% 7.85/2.77  Index Insertion      : 0.00
% 7.85/2.77  Index Deletion       : 0.00
% 7.85/2.77  Index Matching       : 0.00
% 7.85/2.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
