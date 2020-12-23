%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:09 EST 2020

% Result     : Theorem 8.39s
% Output     : CNFRefutation 8.51s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 658 expanded)
%              Number of leaves         :   28 ( 237 expanded)
%              Depth                    :   24
%              Number of atoms          :  335 (2414 expanded)
%              Number of equality atoms :   25 ( 368 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k9_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v2_tex_2(C,A) )
                     => v2_tex_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).

tff(f_103,axiom,(
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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    v2_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_50,plain,(
    v2_tex_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_298,plain,(
    ! [A_90,B_91] :
      ( r1_tarski('#skF_2'(A_90,B_91),B_91)
      | v2_tex_2(B_91,A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_302,plain,
    ( r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_298])).

tff(c_307,plain,
    ( r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_302])).

tff(c_308,plain,(
    r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_307])).

tff(c_26,plain,(
    ! [A_31,B_45] :
      ( m1_subset_1('#skF_2'(A_31,B_45),k1_zfmisc_1(u1_struct_0(A_31)))
      | v2_tex_2(B_45,A_31)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18,plain,(
    ! [A_27] :
      ( m1_pre_topc(A_27,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_95,plain,(
    ! [A_78,B_79] :
      ( m1_pre_topc(A_78,g1_pre_topc(u1_struct_0(B_79),u1_pre_topc(B_79)))
      | ~ m1_pre_topc(A_78,B_79)
      | ~ l1_pre_topc(B_79)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_78,plain,(
    ! [B_75,A_76] :
      ( m1_pre_topc(B_75,A_76)
      | ~ m1_pre_topc(B_75,g1_pre_topc(u1_struct_0(A_76),u1_pre_topc(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [B_75] :
      ( m1_pre_topc(B_75,'#skF_3')
      | ~ m1_pre_topc(B_75,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_78])).

tff(c_87,plain,(
    ! [B_75] :
      ( m1_pre_topc(B_75,'#skF_3')
      | ~ m1_pre_topc(B_75,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_81])).

tff(c_99,plain,(
    ! [A_78] :
      ( m1_pre_topc(A_78,'#skF_3')
      | ~ m1_pre_topc(A_78,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_95,c_87])).

tff(c_111,plain,(
    ! [A_78] :
      ( m1_pre_topc(A_78,'#skF_3')
      | ~ m1_pre_topc(A_78,'#skF_4')
      | ~ l1_pre_topc(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_99])).

tff(c_108,plain,(
    ! [A_78] :
      ( m1_pre_topc(A_78,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_78,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_95])).

tff(c_123,plain,(
    ! [A_81] :
      ( m1_pre_topc(A_81,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_81,'#skF_3')
      | ~ l1_pre_topc(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_108])).

tff(c_10,plain,(
    ! [B_8,A_6] :
      ( m1_pre_topc(B_8,A_6)
      | ~ m1_pre_topc(B_8,g1_pre_topc(u1_struct_0(A_6),u1_pre_topc(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_129,plain,(
    ! [A_81] :
      ( m1_pre_topc(A_81,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(A_81,'#skF_3')
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_123,c_10])).

tff(c_138,plain,(
    ! [A_82] :
      ( m1_pre_topc(A_82,'#skF_4')
      | ~ m1_pre_topc(A_82,'#skF_3')
      | ~ l1_pre_topc(A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_129])).

tff(c_145,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_138])).

tff(c_149,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_145])).

tff(c_20,plain,(
    ! [B_30,A_28] :
      ( r1_tarski(u1_struct_0(B_30),u1_struct_0(A_28))
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_74,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(u1_struct_0(B_73),u1_struct_0(A_74))
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [B_83,A_84] :
      ( u1_struct_0(B_83) = u1_struct_0(A_84)
      | ~ r1_tarski(u1_struct_0(A_84),u1_struct_0(B_83))
      | ~ m1_pre_topc(B_83,A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_74,c_2])).

tff(c_168,plain,(
    ! [B_85,A_86] :
      ( u1_struct_0(B_85) = u1_struct_0(A_86)
      | ~ m1_pre_topc(A_86,B_85)
      | ~ l1_pre_topc(B_85)
      | ~ m1_pre_topc(B_85,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_20,c_157])).

tff(c_170,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_149,c_168])).

tff(c_181,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_170])).

tff(c_189,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_204,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_189])).

tff(c_207,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_204])).

tff(c_210,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_207])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_210])).

tff(c_215,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_642,plain,(
    ! [A_115,B_116,C_117] :
      ( v3_pre_topc('#skF_1'(A_115,B_116,C_117),A_115)
      | ~ r1_tarski(C_117,B_116)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v2_tex_2(B_116,A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_648,plain,(
    ! [B_116,C_117] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_116,C_117),'#skF_3')
      | ~ r1_tarski(C_117,B_116)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_116,'#skF_3')
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_642])).

tff(c_678,plain,(
    ! [B_119,C_120] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_119,C_120),'#skF_3')
      | ~ r1_tarski(C_120,B_119)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_119,'#skF_3')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_215,c_648])).

tff(c_683,plain,(
    ! [B_119,B_45] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_119,'#skF_2'('#skF_4',B_45)),'#skF_3')
      | ~ r1_tarski('#skF_2'('#skF_4',B_45),B_119)
      | ~ v2_tex_2(B_119,'#skF_3')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_45,'#skF_4')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_678])).

tff(c_689,plain,(
    ! [B_119,B_45] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_119,'#skF_2'('#skF_4',B_45)),'#skF_3')
      | ~ r1_tarski('#skF_2'('#skF_4',B_45),B_119)
      | ~ v2_tex_2(B_119,'#skF_3')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_45,'#skF_4')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_683])).

tff(c_216,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_32,plain,(
    ! [A_31,B_45,C_52] :
      ( m1_subset_1('#skF_1'(A_31,B_45,C_52),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ r1_tarski(C_52,B_45)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ v2_tex_2(B_45,A_31)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_743,plain,(
    ! [A_131,B_132,C_133] :
      ( m1_subset_1('#skF_1'(A_131,B_132,C_133),k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ r1_tarski(C_133,B_132)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v2_tex_2(B_132,A_131)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_769,plain,(
    ! [B_132,C_133] :
      ( m1_subset_1('#skF_1'('#skF_3',B_132,C_133),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_133,B_132)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_132,'#skF_3')
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_743])).

tff(c_790,plain,(
    ! [B_134,C_135] :
      ( m1_subset_1('#skF_1'('#skF_3',B_134,C_135),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_135,B_134)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_134,'#skF_3')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_215,c_215,c_769])).

tff(c_16,plain,(
    ! [D_26,C_24,A_12] :
      ( v3_pre_topc(D_26,C_24)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(u1_struct_0(C_24)))
      | ~ v3_pre_topc(D_26,A_12)
      | ~ m1_pre_topc(C_24,A_12)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1738,plain,(
    ! [B_283,C_284,A_285] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_283,C_284),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_283,C_284),A_285)
      | ~ m1_pre_topc('#skF_4',A_285)
      | ~ m1_subset_1('#skF_1'('#skF_3',B_283,C_284),k1_zfmisc_1(u1_struct_0(A_285)))
      | ~ l1_pre_topc(A_285)
      | ~ r1_tarski(C_284,B_283)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_283,'#skF_3')
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_790,c_16])).

tff(c_1748,plain,(
    ! [B_45,C_52] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_45,C_52),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_45,C_52),'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_52,B_45)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_45,'#skF_3')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_1738])).

tff(c_1763,plain,(
    ! [B_286,C_287] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_286,C_287),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_286,C_287),'#skF_3')
      | ~ r1_tarski(C_287,B_286)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_286,'#skF_3')
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_215,c_215,c_216,c_1748])).

tff(c_1865,plain,(
    ! [B_296,B_297] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_296,'#skF_2'('#skF_4',B_297)),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_297),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_297),B_296)
      | ~ v2_tex_2(B_296,'#skF_3')
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_297,'#skF_4')
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_689,c_1763])).

tff(c_1868,plain,(
    ! [B_296,B_45] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_296,'#skF_2'('#skF_4',B_45)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_45),B_296)
      | ~ v2_tex_2(B_296,'#skF_3')
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_45,'#skF_4')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_1865])).

tff(c_1871,plain,(
    ! [B_296,B_45] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_296,'#skF_2'('#skF_4',B_45)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_45),B_296)
      | ~ v2_tex_2(B_296,'#skF_3')
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_45,'#skF_4')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1868])).

tff(c_789,plain,(
    ! [B_132,C_133] :
      ( m1_subset_1('#skF_1'('#skF_3',B_132,C_133),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_133,B_132)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_132,'#skF_3')
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_215,c_215,c_769])).

tff(c_838,plain,(
    ! [A_141,B_142,C_143] :
      ( k9_subset_1(u1_struct_0(A_141),B_142,'#skF_1'(A_141,B_142,C_143)) = C_143
      | ~ r1_tarski(C_143,B_142)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ v2_tex_2(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_848,plain,(
    ! [B_142,C_143] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_142,'#skF_1'('#skF_3',B_142,C_143)) = C_143
      | ~ r1_tarski(C_143,B_142)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_142,'#skF_3')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_838])).

tff(c_888,plain,(
    ! [B_145,C_146] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_145,'#skF_1'('#skF_3',B_145,C_146)) = C_146
      | ~ r1_tarski(C_146,B_145)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_145,'#skF_3')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_215,c_215,c_848])).

tff(c_898,plain,(
    ! [B_145,B_45] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_145,'#skF_1'('#skF_3',B_145,'#skF_2'('#skF_4',B_45))) = '#skF_2'('#skF_4',B_45)
      | ~ r1_tarski('#skF_2'('#skF_4',B_45),B_145)
      | ~ v2_tex_2(B_145,'#skF_3')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_45,'#skF_4')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_888])).

tff(c_1503,plain,(
    ! [B_225,B_226] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_225,'#skF_1'('#skF_3',B_225,'#skF_2'('#skF_4',B_226))) = '#skF_2'('#skF_4',B_226)
      | ~ r1_tarski('#skF_2'('#skF_4',B_226),B_225)
      | ~ v2_tex_2(B_225,'#skF_3')
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_226,'#skF_4')
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_898])).

tff(c_22,plain,(
    ! [A_31,B_45,D_55] :
      ( k9_subset_1(u1_struct_0(A_31),B_45,D_55) != '#skF_2'(A_31,B_45)
      | ~ v3_pre_topc(D_55,A_31)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0(A_31)))
      | v2_tex_2(B_45,A_31)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1510,plain,(
    ! [B_226,B_225] :
      ( '#skF_2'('#skF_4',B_226) != '#skF_2'('#skF_4',B_225)
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_225,'#skF_2'('#skF_4',B_226)),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_225,'#skF_2'('#skF_4',B_226)),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_225,'#skF_4')
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_226),B_225)
      | ~ v2_tex_2(B_225,'#skF_3')
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_226,'#skF_4')
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1503,c_22])).

tff(c_3013,plain,(
    ! [B_432,B_431] :
      ( '#skF_2'('#skF_4',B_432) != '#skF_2'('#skF_4',B_431)
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_432,'#skF_2'('#skF_4',B_431)),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_432,'#skF_2'('#skF_4',B_431)),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_432,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_431),B_432)
      | ~ v2_tex_2(B_432,'#skF_3')
      | ~ m1_subset_1(B_432,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_431,'#skF_4')
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1510])).

tff(c_3160,plain,(
    ! [B_435,B_434] :
      ( '#skF_2'('#skF_4',B_435) != '#skF_2'('#skF_4',B_434)
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_435,'#skF_2'('#skF_4',B_434)),'#skF_4')
      | v2_tex_2(B_435,'#skF_4')
      | v2_tex_2(B_434,'#skF_4')
      | ~ m1_subset_1(B_434,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_434),B_435)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_434),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_435,'#skF_3')
      | ~ m1_subset_1(B_435,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_789,c_3013])).

tff(c_3164,plain,(
    ! [B_437,B_436] :
      ( '#skF_2'('#skF_4',B_437) != '#skF_2'('#skF_4',B_436)
      | v2_tex_2(B_437,'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_436),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_436),B_437)
      | ~ v2_tex_2(B_437,'#skF_3')
      | ~ m1_subset_1(B_437,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_436,'#skF_4')
      | ~ m1_subset_1(B_436,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1871,c_3160])).

tff(c_3167,plain,(
    ! [B_45,B_437] :
      ( '#skF_2'('#skF_4',B_45) != '#skF_2'('#skF_4',B_437)
      | v2_tex_2(B_437,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_45),B_437)
      | ~ v2_tex_2(B_437,'#skF_3')
      | ~ m1_subset_1(B_437,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_45,'#skF_4')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_3164])).

tff(c_3171,plain,(
    ! [B_439,B_438] :
      ( '#skF_2'('#skF_4',B_439) != '#skF_2'('#skF_4',B_438)
      | v2_tex_2(B_439,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_438),B_439)
      | ~ v2_tex_2(B_439,'#skF_3')
      | ~ m1_subset_1(B_439,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_438,'#skF_4')
      | ~ m1_subset_1(B_438,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3167])).

tff(c_3183,plain,
    ( ~ v2_tex_2('#skF_6','#skF_3')
    | v2_tex_2('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_308,c_3171])).

tff(c_3197,plain,(
    v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_50,c_3183])).

tff(c_3199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:54:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.39/2.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.39/2.92  
% 8.39/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.39/2.92  %$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k9_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 8.39/2.92  
% 8.39/2.92  %Foreground sorts:
% 8.39/2.92  
% 8.39/2.92  
% 8.39/2.92  %Background operators:
% 8.39/2.92  
% 8.39/2.92  
% 8.39/2.92  %Foreground operators:
% 8.39/2.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.39/2.92  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.39/2.92  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.39/2.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.39/2.92  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 8.39/2.92  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.39/2.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.39/2.92  tff('#skF_5', type, '#skF_5': $i).
% 8.39/2.92  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.39/2.92  tff('#skF_6', type, '#skF_6': $i).
% 8.39/2.92  tff('#skF_3', type, '#skF_3': $i).
% 8.39/2.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.39/2.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.39/2.92  tff('#skF_4', type, '#skF_4': $i).
% 8.39/2.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.39/2.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.39/2.92  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.39/2.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.39/2.92  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.39/2.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.39/2.92  
% 8.51/2.94  tff(f_123, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tex_2(C, A)) => v2_tex_2(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tex_2)).
% 8.51/2.94  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 8.51/2.94  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 8.51/2.94  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 8.51/2.94  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 8.51/2.94  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 8.51/2.94  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.51/2.94  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 8.51/2.94  tff(c_34, plain, (~v2_tex_2('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.51/2.94  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.51/2.94  tff(c_38, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.51/2.94  tff(c_36, plain, (v2_tex_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.51/2.94  tff(c_50, plain, (v2_tex_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 8.51/2.94  tff(c_46, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.51/2.94  tff(c_298, plain, (![A_90, B_91]: (r1_tarski('#skF_2'(A_90, B_91), B_91) | v2_tex_2(B_91, A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.51/2.94  tff(c_302, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_42, c_298])).
% 8.51/2.94  tff(c_307, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_302])).
% 8.51/2.94  tff(c_308, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_34, c_307])).
% 8.51/2.94  tff(c_26, plain, (![A_31, B_45]: (m1_subset_1('#skF_2'(A_31, B_45), k1_zfmisc_1(u1_struct_0(A_31))) | v2_tex_2(B_45, A_31) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.51/2.94  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.51/2.94  tff(c_18, plain, (![A_27]: (m1_pre_topc(A_27, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.51/2.94  tff(c_95, plain, (![A_78, B_79]: (m1_pre_topc(A_78, g1_pre_topc(u1_struct_0(B_79), u1_pre_topc(B_79))) | ~m1_pre_topc(A_78, B_79) | ~l1_pre_topc(B_79) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.51/2.94  tff(c_40, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.51/2.94  tff(c_78, plain, (![B_75, A_76]: (m1_pre_topc(B_75, A_76) | ~m1_pre_topc(B_75, g1_pre_topc(u1_struct_0(A_76), u1_pre_topc(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.51/2.94  tff(c_81, plain, (![B_75]: (m1_pre_topc(B_75, '#skF_3') | ~m1_pre_topc(B_75, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_78])).
% 8.51/2.94  tff(c_87, plain, (![B_75]: (m1_pre_topc(B_75, '#skF_3') | ~m1_pre_topc(B_75, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_81])).
% 8.51/2.94  tff(c_99, plain, (![A_78]: (m1_pre_topc(A_78, '#skF_3') | ~m1_pre_topc(A_78, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_95, c_87])).
% 8.51/2.94  tff(c_111, plain, (![A_78]: (m1_pre_topc(A_78, '#skF_3') | ~m1_pre_topc(A_78, '#skF_4') | ~l1_pre_topc(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_99])).
% 8.51/2.94  tff(c_108, plain, (![A_78]: (m1_pre_topc(A_78, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_78, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_78))), inference(superposition, [status(thm), theory('equality')], [c_40, c_95])).
% 8.51/2.94  tff(c_123, plain, (![A_81]: (m1_pre_topc(A_81, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_81, '#skF_3') | ~l1_pre_topc(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_108])).
% 8.51/2.94  tff(c_10, plain, (![B_8, A_6]: (m1_pre_topc(B_8, A_6) | ~m1_pre_topc(B_8, g1_pre_topc(u1_struct_0(A_6), u1_pre_topc(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.51/2.94  tff(c_129, plain, (![A_81]: (m1_pre_topc(A_81, '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(A_81, '#skF_3') | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_123, c_10])).
% 8.51/2.94  tff(c_138, plain, (![A_82]: (m1_pre_topc(A_82, '#skF_4') | ~m1_pre_topc(A_82, '#skF_3') | ~l1_pre_topc(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_129])).
% 8.51/2.94  tff(c_145, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_138])).
% 8.51/2.94  tff(c_149, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_145])).
% 8.51/2.94  tff(c_20, plain, (![B_30, A_28]: (r1_tarski(u1_struct_0(B_30), u1_struct_0(A_28)) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.51/2.94  tff(c_74, plain, (![B_73, A_74]: (r1_tarski(u1_struct_0(B_73), u1_struct_0(A_74)) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.51/2.94  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.51/2.94  tff(c_157, plain, (![B_83, A_84]: (u1_struct_0(B_83)=u1_struct_0(A_84) | ~r1_tarski(u1_struct_0(A_84), u1_struct_0(B_83)) | ~m1_pre_topc(B_83, A_84) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_74, c_2])).
% 8.51/2.94  tff(c_168, plain, (![B_85, A_86]: (u1_struct_0(B_85)=u1_struct_0(A_86) | ~m1_pre_topc(A_86, B_85) | ~l1_pre_topc(B_85) | ~m1_pre_topc(B_85, A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_20, c_157])).
% 8.51/2.94  tff(c_170, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_149, c_168])).
% 8.51/2.94  tff(c_181, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_170])).
% 8.51/2.94  tff(c_189, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_181])).
% 8.51/2.94  tff(c_204, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_111, c_189])).
% 8.51/2.94  tff(c_207, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_204])).
% 8.51/2.94  tff(c_210, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_207])).
% 8.51/2.94  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_210])).
% 8.51/2.94  tff(c_215, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_181])).
% 8.51/2.94  tff(c_642, plain, (![A_115, B_116, C_117]: (v3_pre_topc('#skF_1'(A_115, B_116, C_117), A_115) | ~r1_tarski(C_117, B_116) | ~m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0(A_115))) | ~v2_tex_2(B_116, A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.51/2.94  tff(c_648, plain, (![B_116, C_117]: (v3_pre_topc('#skF_1'('#skF_3', B_116, C_117), '#skF_3') | ~r1_tarski(C_117, B_116) | ~m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_116, '#skF_3') | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_215, c_642])).
% 8.51/2.94  tff(c_678, plain, (![B_119, C_120]: (v3_pre_topc('#skF_1'('#skF_3', B_119, C_120), '#skF_3') | ~r1_tarski(C_120, B_119) | ~m1_subset_1(C_120, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_119, '#skF_3') | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_215, c_648])).
% 8.51/2.94  tff(c_683, plain, (![B_119, B_45]: (v3_pre_topc('#skF_1'('#skF_3', B_119, '#skF_2'('#skF_4', B_45)), '#skF_3') | ~r1_tarski('#skF_2'('#skF_4', B_45), B_119) | ~v2_tex_2(B_119, '#skF_3') | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_45, '#skF_4') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_678])).
% 8.51/2.94  tff(c_689, plain, (![B_119, B_45]: (v3_pre_topc('#skF_1'('#skF_3', B_119, '#skF_2'('#skF_4', B_45)), '#skF_3') | ~r1_tarski('#skF_2'('#skF_4', B_45), B_119) | ~v2_tex_2(B_119, '#skF_3') | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_45, '#skF_4') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_683])).
% 8.51/2.94  tff(c_216, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_181])).
% 8.51/2.94  tff(c_32, plain, (![A_31, B_45, C_52]: (m1_subset_1('#skF_1'(A_31, B_45, C_52), k1_zfmisc_1(u1_struct_0(A_31))) | ~r1_tarski(C_52, B_45) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(A_31))) | ~v2_tex_2(B_45, A_31) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.51/2.94  tff(c_743, plain, (![A_131, B_132, C_133]: (m1_subset_1('#skF_1'(A_131, B_132, C_133), k1_zfmisc_1(u1_struct_0(A_131))) | ~r1_tarski(C_133, B_132) | ~m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0(A_131))) | ~v2_tex_2(B_132, A_131) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.51/2.94  tff(c_769, plain, (![B_132, C_133]: (m1_subset_1('#skF_1'('#skF_3', B_132, C_133), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_133, B_132) | ~m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_132, '#skF_3') | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_215, c_743])).
% 8.51/2.94  tff(c_790, plain, (![B_134, C_135]: (m1_subset_1('#skF_1'('#skF_3', B_134, C_135), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_135, B_134) | ~m1_subset_1(C_135, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_134, '#skF_3') | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_215, c_215, c_769])).
% 8.51/2.94  tff(c_16, plain, (![D_26, C_24, A_12]: (v3_pre_topc(D_26, C_24) | ~m1_subset_1(D_26, k1_zfmisc_1(u1_struct_0(C_24))) | ~v3_pre_topc(D_26, A_12) | ~m1_pre_topc(C_24, A_12) | ~m1_subset_1(D_26, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.51/2.94  tff(c_1738, plain, (![B_283, C_284, A_285]: (v3_pre_topc('#skF_1'('#skF_3', B_283, C_284), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_3', B_283, C_284), A_285) | ~m1_pre_topc('#skF_4', A_285) | ~m1_subset_1('#skF_1'('#skF_3', B_283, C_284), k1_zfmisc_1(u1_struct_0(A_285))) | ~l1_pre_topc(A_285) | ~r1_tarski(C_284, B_283) | ~m1_subset_1(C_284, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_283, '#skF_3') | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_790, c_16])).
% 8.51/2.94  tff(c_1748, plain, (![B_45, C_52]: (v3_pre_topc('#skF_1'('#skF_3', B_45, C_52), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_3', B_45, C_52), '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_52, B_45) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_45, '#skF_3') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_1738])).
% 8.51/2.94  tff(c_1763, plain, (![B_286, C_287]: (v3_pre_topc('#skF_1'('#skF_3', B_286, C_287), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_3', B_286, C_287), '#skF_3') | ~r1_tarski(C_287, B_286) | ~m1_subset_1(C_287, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_286, '#skF_3') | ~m1_subset_1(B_286, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_215, c_215, c_216, c_1748])).
% 8.51/2.94  tff(c_1865, plain, (![B_296, B_297]: (v3_pre_topc('#skF_1'('#skF_3', B_296, '#skF_2'('#skF_4', B_297)), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', B_297), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_4', B_297), B_296) | ~v2_tex_2(B_296, '#skF_3') | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_297, '#skF_4') | ~m1_subset_1(B_297, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_689, c_1763])).
% 8.51/2.94  tff(c_1868, plain, (![B_296, B_45]: (v3_pre_topc('#skF_1'('#skF_3', B_296, '#skF_2'('#skF_4', B_45)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_45), B_296) | ~v2_tex_2(B_296, '#skF_3') | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_45, '#skF_4') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_1865])).
% 8.51/2.94  tff(c_1871, plain, (![B_296, B_45]: (v3_pre_topc('#skF_1'('#skF_3', B_296, '#skF_2'('#skF_4', B_45)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_45), B_296) | ~v2_tex_2(B_296, '#skF_3') | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_45, '#skF_4') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1868])).
% 8.51/2.94  tff(c_789, plain, (![B_132, C_133]: (m1_subset_1('#skF_1'('#skF_3', B_132, C_133), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_133, B_132) | ~m1_subset_1(C_133, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_132, '#skF_3') | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_215, c_215, c_769])).
% 8.51/2.94  tff(c_838, plain, (![A_141, B_142, C_143]: (k9_subset_1(u1_struct_0(A_141), B_142, '#skF_1'(A_141, B_142, C_143))=C_143 | ~r1_tarski(C_143, B_142) | ~m1_subset_1(C_143, k1_zfmisc_1(u1_struct_0(A_141))) | ~v2_tex_2(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.51/2.94  tff(c_848, plain, (![B_142, C_143]: (k9_subset_1(u1_struct_0('#skF_3'), B_142, '#skF_1'('#skF_3', B_142, C_143))=C_143 | ~r1_tarski(C_143, B_142) | ~m1_subset_1(C_143, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_142, '#skF_3') | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_215, c_838])).
% 8.51/2.94  tff(c_888, plain, (![B_145, C_146]: (k9_subset_1(u1_struct_0('#skF_4'), B_145, '#skF_1'('#skF_3', B_145, C_146))=C_146 | ~r1_tarski(C_146, B_145) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_145, '#skF_3') | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_215, c_215, c_848])).
% 8.51/2.94  tff(c_898, plain, (![B_145, B_45]: (k9_subset_1(u1_struct_0('#skF_4'), B_145, '#skF_1'('#skF_3', B_145, '#skF_2'('#skF_4', B_45)))='#skF_2'('#skF_4', B_45) | ~r1_tarski('#skF_2'('#skF_4', B_45), B_145) | ~v2_tex_2(B_145, '#skF_3') | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_45, '#skF_4') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_888])).
% 8.51/2.94  tff(c_1503, plain, (![B_225, B_226]: (k9_subset_1(u1_struct_0('#skF_4'), B_225, '#skF_1'('#skF_3', B_225, '#skF_2'('#skF_4', B_226)))='#skF_2'('#skF_4', B_226) | ~r1_tarski('#skF_2'('#skF_4', B_226), B_225) | ~v2_tex_2(B_225, '#skF_3') | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_226, '#skF_4') | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_898])).
% 8.51/2.94  tff(c_22, plain, (![A_31, B_45, D_55]: (k9_subset_1(u1_struct_0(A_31), B_45, D_55)!='#skF_2'(A_31, B_45) | ~v3_pre_topc(D_55, A_31) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0(A_31))) | v2_tex_2(B_45, A_31) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.51/2.94  tff(c_1510, plain, (![B_226, B_225]: ('#skF_2'('#skF_4', B_226)!='#skF_2'('#skF_4', B_225) | ~v3_pre_topc('#skF_1'('#skF_3', B_225, '#skF_2'('#skF_4', B_226)), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', B_225, '#skF_2'('#skF_4', B_226)), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_225, '#skF_4') | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_226), B_225) | ~v2_tex_2(B_225, '#skF_3') | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_226, '#skF_4') | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_1503, c_22])).
% 8.51/2.94  tff(c_3013, plain, (![B_432, B_431]: ('#skF_2'('#skF_4', B_432)!='#skF_2'('#skF_4', B_431) | ~v3_pre_topc('#skF_1'('#skF_3', B_432, '#skF_2'('#skF_4', B_431)), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', B_432, '#skF_2'('#skF_4', B_431)), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_432, '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_431), B_432) | ~v2_tex_2(B_432, '#skF_3') | ~m1_subset_1(B_432, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_431, '#skF_4') | ~m1_subset_1(B_431, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1510])).
% 8.51/2.94  tff(c_3160, plain, (![B_435, B_434]: ('#skF_2'('#skF_4', B_435)!='#skF_2'('#skF_4', B_434) | ~v3_pre_topc('#skF_1'('#skF_3', B_435, '#skF_2'('#skF_4', B_434)), '#skF_4') | v2_tex_2(B_435, '#skF_4') | v2_tex_2(B_434, '#skF_4') | ~m1_subset_1(B_434, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_4', B_434), B_435) | ~m1_subset_1('#skF_2'('#skF_4', B_434), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_435, '#skF_3') | ~m1_subset_1(B_435, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_789, c_3013])).
% 8.51/2.94  tff(c_3164, plain, (![B_437, B_436]: ('#skF_2'('#skF_4', B_437)!='#skF_2'('#skF_4', B_436) | v2_tex_2(B_437, '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', B_436), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_4', B_436), B_437) | ~v2_tex_2(B_437, '#skF_3') | ~m1_subset_1(B_437, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_436, '#skF_4') | ~m1_subset_1(B_436, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1871, c_3160])).
% 8.51/2.94  tff(c_3167, plain, (![B_45, B_437]: ('#skF_2'('#skF_4', B_45)!='#skF_2'('#skF_4', B_437) | v2_tex_2(B_437, '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_45), B_437) | ~v2_tex_2(B_437, '#skF_3') | ~m1_subset_1(B_437, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_45, '#skF_4') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_3164])).
% 8.51/2.94  tff(c_3171, plain, (![B_439, B_438]: ('#skF_2'('#skF_4', B_439)!='#skF_2'('#skF_4', B_438) | v2_tex_2(B_439, '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_438), B_439) | ~v2_tex_2(B_439, '#skF_3') | ~m1_subset_1(B_439, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_438, '#skF_4') | ~m1_subset_1(B_438, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3167])).
% 8.51/2.94  tff(c_3183, plain, (~v2_tex_2('#skF_6', '#skF_3') | v2_tex_2('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_308, c_3171])).
% 8.51/2.94  tff(c_3197, plain, (v2_tex_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_50, c_3183])).
% 8.51/2.94  tff(c_3199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_3197])).
% 8.51/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.51/2.94  
% 8.51/2.94  Inference rules
% 8.51/2.94  ----------------------
% 8.51/2.94  #Ref     : 0
% 8.51/2.94  #Sup     : 608
% 8.51/2.94  #Fact    : 0
% 8.51/2.94  #Define  : 0
% 8.51/2.94  #Split   : 13
% 8.51/2.94  #Chain   : 0
% 8.51/2.94  #Close   : 0
% 8.51/2.94  
% 8.51/2.94  Ordering : KBO
% 8.51/2.94  
% 8.51/2.94  Simplification rules
% 8.51/2.94  ----------------------
% 8.51/2.94  #Subsume      : 199
% 8.51/2.94  #Demod        : 4437
% 8.51/2.94  #Tautology    : 170
% 8.51/2.94  #SimpNegUnit  : 12
% 8.51/2.94  #BackRed      : 2
% 8.51/2.94  
% 8.51/2.94  #Partial instantiations: 0
% 8.51/2.94  #Strategies tried      : 1
% 8.51/2.94  
% 8.51/2.94  Timing (in seconds)
% 8.51/2.94  ----------------------
% 8.51/2.95  Preprocessing        : 0.35
% 8.51/2.95  Parsing              : 0.19
% 8.51/2.95  CNF conversion       : 0.03
% 8.51/2.95  Main loop            : 1.77
% 8.51/2.95  Inferencing          : 0.53
% 8.51/2.95  Reduction            : 0.74
% 8.51/2.95  Demodulation         : 0.60
% 8.51/2.95  BG Simplification    : 0.04
% 8.51/2.95  Subsumption          : 0.39
% 8.51/2.95  Abstraction          : 0.06
% 8.51/2.95  MUC search           : 0.00
% 8.51/2.95  Cooper               : 0.00
% 8.51/2.95  Total                : 2.16
% 8.51/2.95  Index Insertion      : 0.00
% 8.51/2.95  Index Deletion       : 0.00
% 8.51/2.95  Index Matching       : 0.00
% 8.51/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
