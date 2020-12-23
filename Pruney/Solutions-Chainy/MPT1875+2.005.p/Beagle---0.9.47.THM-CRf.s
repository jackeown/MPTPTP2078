%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:47 EST 2020

% Result     : Theorem 37.04s
% Output     : CNFRefutation 37.20s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 376 expanded)
%              Number of leaves         :   45 ( 146 expanded)
%              Depth                    :   18
%              Number of atoms          :  309 (1020 expanded)
%              Number of equality atoms :   24 (  69 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_192,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_46,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_163,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_connsp_1)).

tff(f_55,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_177,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_tex_2(B,A)
                  | v2_tex_2(C,A) )
               => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_borsuk_1(B,A)
            & v1_tsep_1(B,A)
            & v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_70,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_72,plain,(
    v1_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_16,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_58,plain,(
    ! [A_48] :
      ( v2_tex_2(u1_struct_0(A_48),A_48)
      | ~ v1_tdlat_3(A_48)
      | ~ m1_subset_1(u1_struct_0(A_48),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_81,plain,(
    ! [A_48] :
      ( v2_tex_2(u1_struct_0(A_48),A_48)
      | ~ v1_tdlat_3(A_48)
      | ~ l1_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_58])).

tff(c_66,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2599,plain,(
    ! [A_244,B_245] :
      ( v1_pre_topc('#skF_4'(A_244,B_245))
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_244)))
      | v1_xboole_0(B_245)
      | ~ l1_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2627,plain,
    ( v1_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_2599])).

tff(c_2648,plain,
    ( v1_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2627])).

tff(c_2649,plain,
    ( v1_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2648])).

tff(c_2652,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2649])).

tff(c_1181,plain,(
    ! [A_157,B_158,C_159] :
      ( k9_subset_1(A_157,B_158,C_159) = k3_xboole_0(B_158,C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(A_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1211,plain,(
    ! [A_12,B_158] : k9_subset_1(A_12,B_158,A_12) = k3_xboole_0(B_158,A_12) ),
    inference(resolution,[status(thm)],[c_77,c_1181])).

tff(c_1502,plain,(
    ! [A_177,B_178,C_179] :
      ( m1_subset_1(k9_subset_1(A_177,B_178,C_179),k1_zfmisc_1(A_177))
      | ~ m1_subset_1(C_179,k1_zfmisc_1(A_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1518,plain,(
    ! [B_158,A_12] :
      ( m1_subset_1(k3_xboole_0(B_158,A_12),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(A_12,k1_zfmisc_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1211,c_1502])).

tff(c_1526,plain,(
    ! [B_180,A_181] : m1_subset_1(k3_xboole_0(B_180,A_181),k1_zfmisc_1(A_181)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1518])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1537,plain,(
    ! [B_182,A_183] : r1_tarski(k3_xboole_0(B_182,A_183),A_183) ),
    inference(resolution,[status(thm)],[c_1526,c_26])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_149,plain,(
    ! [C_78,B_79,A_80] :
      ( ~ v1_xboole_0(C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_166,plain,(
    ! [A_81,A_82] :
      ( ~ v1_xboole_0(A_81)
      | ~ r2_hidden(A_82,A_81) ) ),
    inference(resolution,[status(thm)],[c_77,c_149])).

tff(c_184,plain,(
    ! [A_86,B_87] :
      ( ~ v1_xboole_0(A_86)
      | r1_tarski(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_194,plain,(
    ! [B_87,A_86] :
      ( B_87 = A_86
      | ~ r1_tarski(B_87,A_86)
      | ~ v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_184,c_8])).

tff(c_1572,plain,(
    ! [B_182,A_183] :
      ( k3_xboole_0(B_182,A_183) = A_183
      | ~ v1_xboole_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_1537,c_194])).

tff(c_2672,plain,(
    ! [B_182] : k3_xboole_0(B_182,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2652,c_1572])).

tff(c_32,plain,(
    ! [A_26] :
      ( v1_xboole_0('#skF_3'(A_26))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_16] : m1_subset_1('#skF_2'(A_16),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_202,plain,(
    ! [C_89,A_90] :
      ( ~ v1_xboole_0(C_89)
      | ~ r2_hidden(A_90,'#skF_2'(k1_zfmisc_1(C_89))) ) ),
    inference(resolution,[status(thm)],[c_22,c_149])).

tff(c_207,plain,(
    ! [C_89,B_2] :
      ( ~ v1_xboole_0(C_89)
      | r1_tarski('#skF_2'(k1_zfmisc_1(C_89)),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_202])).

tff(c_215,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ v1_xboole_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_184,c_8])).

tff(c_429,plain,(
    ! [B_115,C_116] :
      ( B_115 = '#skF_2'(k1_zfmisc_1(C_116))
      | ~ v1_xboole_0(B_115)
      | ~ v1_xboole_0(C_116) ) ),
    inference(resolution,[status(thm)],[c_207,c_215])).

tff(c_660,plain,(
    ! [A_134,C_135] :
      ( '#skF_3'(A_134) = '#skF_2'(k1_zfmisc_1(C_135))
      | ~ v1_xboole_0(C_135)
      | ~ l1_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_32,c_429])).

tff(c_664,plain,(
    ! [C_136] :
      ( '#skF_2'(k1_zfmisc_1(C_136)) = '#skF_3'('#skF_5')
      | ~ v1_xboole_0(C_136) ) ),
    inference(resolution,[status(thm)],[c_70,c_660])).

tff(c_98,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_116,plain,(
    ! [B_68] : r1_tarski('#skF_2'(k1_zfmisc_1(B_68)),B_68) ),
    inference(resolution,[status(thm)],[c_22,c_98])).

tff(c_733,plain,(
    ! [C_137] :
      ( r1_tarski('#skF_3'('#skF_5'),C_137)
      | ~ v1_xboole_0(C_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_116])).

tff(c_757,plain,(
    ! [C_137] :
      ( C_137 = '#skF_3'('#skF_5')
      | ~ v1_xboole_0(C_137) ) ),
    inference(resolution,[status(thm)],[c_733,c_194])).

tff(c_2674,plain,(
    '#skF_3'('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2652,c_757])).

tff(c_34,plain,(
    ! [A_26] :
      ( m1_subset_1('#skF_3'(A_26),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10314,plain,(
    ! [A_442,B_443] :
      ( k9_subset_1(u1_struct_0(A_442),B_443,'#skF_3'(A_442)) = k3_xboole_0(B_443,'#skF_3'(A_442))
      | ~ l1_pre_topc(A_442) ) ),
    inference(resolution,[status(thm)],[c_34,c_1181])).

tff(c_64,plain,(
    ! [B_55,A_51,C_57] :
      ( ~ v2_tex_2(B_55,A_51)
      | v2_tex_2(k9_subset_1(u1_struct_0(A_51),B_55,C_57),A_51)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_153349,plain,(
    ! [B_1698,A_1699] :
      ( ~ v2_tex_2(B_1698,A_1699)
      | v2_tex_2(k3_xboole_0(B_1698,'#skF_3'(A_1699)),A_1699)
      | ~ m1_subset_1('#skF_3'(A_1699),k1_zfmisc_1(u1_struct_0(A_1699)))
      | ~ m1_subset_1(B_1698,k1_zfmisc_1(u1_struct_0(A_1699)))
      | ~ l1_pre_topc(A_1699)
      | ~ l1_pre_topc(A_1699) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10314,c_64])).

tff(c_153379,plain,(
    ! [B_1698] :
      ( ~ v2_tex_2(B_1698,'#skF_5')
      | v2_tex_2(k3_xboole_0(B_1698,'#skF_3'('#skF_5')),'#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1698,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2674,c_153349])).

tff(c_153388,plain,(
    ! [B_1698] :
      ( ~ v2_tex_2(B_1698,'#skF_5')
      | v2_tex_2('#skF_6','#skF_5')
      | ~ m1_subset_1(B_1698,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_68,c_2672,c_2674,c_153379])).

tff(c_153392,plain,(
    ! [B_1700] :
      ( ~ v2_tex_2(B_1700,'#skF_5')
      | ~ m1_subset_1(B_1700,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_153388])).

tff(c_153543,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_77,c_153392])).

tff(c_153550,plain,
    ( ~ v1_tdlat_3('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_81,c_153543])).

tff(c_153557,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_153550])).

tff(c_153559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_153557])).

tff(c_153561,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2649])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_98])).

tff(c_171,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_tarski(A_83,C_84)
      | ~ r1_tarski(B_85,C_84)
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_182,plain,(
    ! [A_83] :
      ( r1_tarski(A_83,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_83,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_113,c_171])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_154395,plain,(
    ! [A_1732,B_1733] :
      ( m1_pre_topc('#skF_4'(A_1732,B_1733),A_1732)
      | ~ m1_subset_1(B_1733,k1_zfmisc_1(u1_struct_0(A_1732)))
      | v1_xboole_0(B_1733)
      | ~ l1_pre_topc(A_1732)
      | v2_struct_0(A_1732) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_169609,plain,(
    ! [A_2029,A_2030] :
      ( m1_pre_topc('#skF_4'(A_2029,A_2030),A_2029)
      | v1_xboole_0(A_2030)
      | ~ l1_pre_topc(A_2029)
      | v2_struct_0(A_2029)
      | ~ r1_tarski(A_2030,u1_struct_0(A_2029)) ) ),
    inference(resolution,[status(thm)],[c_28,c_154395])).

tff(c_169753,plain,(
    ! [A_83] :
      ( m1_pre_topc('#skF_4'('#skF_5',A_83),'#skF_5')
      | v1_xboole_0(A_83)
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_83,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_182,c_169609])).

tff(c_169866,plain,(
    ! [A_83] :
      ( m1_pre_topc('#skF_4'('#skF_5',A_83),'#skF_5')
      | v1_xboole_0(A_83)
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(A_83,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_169753])).

tff(c_169867,plain,(
    ! [A_83] :
      ( m1_pre_topc('#skF_4'('#skF_5',A_83),'#skF_5')
      | v1_xboole_0(A_83)
      | ~ r1_tarski(A_83,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_169866])).

tff(c_153811,plain,(
    ! [A_1709,B_1710] :
      ( ~ v2_struct_0('#skF_4'(A_1709,B_1710))
      | ~ m1_subset_1(B_1710,k1_zfmisc_1(u1_struct_0(A_1709)))
      | v1_xboole_0(B_1710)
      | ~ l1_pre_topc(A_1709)
      | v2_struct_0(A_1709) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_153839,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_153811])).

tff(c_153860,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_153839])).

tff(c_153861,plain,(
    ~ v2_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_153561,c_153860])).

tff(c_74,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_154415,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_154395])).

tff(c_154434,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_154415])).

tff(c_154435,plain,(
    m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_153561,c_154434])).

tff(c_40,plain,(
    ! [B_34,A_32] :
      ( v1_tdlat_3(B_34)
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32)
      | ~ v1_tdlat_3(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_154440,plain,
    ( v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v1_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_154435,c_40])).

tff(c_154443,plain,
    ( v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_154440])).

tff(c_154444,plain,(
    v1_tdlat_3('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_154443])).

tff(c_155014,plain,(
    ! [A_1748,B_1749] :
      ( u1_struct_0('#skF_4'(A_1748,B_1749)) = B_1749
      | ~ m1_subset_1(B_1749,k1_zfmisc_1(u1_struct_0(A_1748)))
      | v1_xboole_0(B_1749)
      | ~ l1_pre_topc(A_1748)
      | v2_struct_0(A_1748) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_155042,plain,
    ( u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_155014])).

tff(c_155063,plain,
    ( u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_155042])).

tff(c_155064,plain,(
    u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_153561,c_155063])).

tff(c_36,plain,(
    ! [B_30,A_28] :
      ( m1_subset_1(u1_struct_0(B_30),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_155503,plain,(
    ! [B_1758,A_1759] :
      ( v2_tex_2(u1_struct_0(B_1758),A_1759)
      | ~ v1_tdlat_3(B_1758)
      | ~ m1_subset_1(u1_struct_0(B_1758),k1_zfmisc_1(u1_struct_0(A_1759)))
      | ~ m1_pre_topc(B_1758,A_1759)
      | v2_struct_0(B_1758)
      | ~ l1_pre_topc(A_1759)
      | v2_struct_0(A_1759) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_171775,plain,(
    ! [B_2066,A_2067] :
      ( v2_tex_2(u1_struct_0(B_2066),A_2067)
      | ~ v1_tdlat_3(B_2066)
      | v2_struct_0(B_2066)
      | v2_struct_0(A_2067)
      | ~ m1_pre_topc(B_2066,A_2067)
      | ~ l1_pre_topc(A_2067) ) ),
    inference(resolution,[status(thm)],[c_36,c_155503])).

tff(c_171791,plain,(
    ! [A_2067] :
      ( v2_tex_2('#skF_6',A_2067)
      | ~ v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
      | v2_struct_0('#skF_4'('#skF_5','#skF_6'))
      | v2_struct_0(A_2067)
      | ~ m1_pre_topc('#skF_4'('#skF_5','#skF_6'),A_2067)
      | ~ l1_pre_topc(A_2067) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155064,c_171775])).

tff(c_171795,plain,(
    ! [A_2067] :
      ( v2_tex_2('#skF_6',A_2067)
      | v2_struct_0('#skF_4'('#skF_5','#skF_6'))
      | v2_struct_0(A_2067)
      | ~ m1_pre_topc('#skF_4'('#skF_5','#skF_6'),A_2067)
      | ~ l1_pre_topc(A_2067) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154444,c_171791])).

tff(c_188345,plain,(
    ! [A_2286] :
      ( v2_tex_2('#skF_6',A_2286)
      | v2_struct_0(A_2286)
      | ~ m1_pre_topc('#skF_4'('#skF_5','#skF_6'),A_2286)
      | ~ l1_pre_topc(A_2286) ) ),
    inference(negUnitSimplification,[status(thm)],[c_153861,c_171795])).

tff(c_188349,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_169867,c_188345])).

tff(c_188355,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_70,c_188349])).

tff(c_188357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_153561,c_76,c_66,c_188355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:32:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.04/27.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.04/27.22  
% 37.04/27.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.04/27.22  %$ v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 37.04/27.22  
% 37.04/27.22  %Foreground sorts:
% 37.04/27.22  
% 37.04/27.22  
% 37.04/27.22  %Background operators:
% 37.04/27.22  
% 37.04/27.22  
% 37.04/27.22  %Foreground operators:
% 37.04/27.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 37.04/27.22  tff('#skF_2', type, '#skF_2': $i > $i).
% 37.04/27.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.04/27.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 37.04/27.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 37.04/27.22  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 37.04/27.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 37.04/27.22  tff('#skF_5', type, '#skF_5': $i).
% 37.04/27.22  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 37.04/27.22  tff('#skF_6', type, '#skF_6': $i).
% 37.04/27.22  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 37.04/27.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 37.04/27.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.04/27.22  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 37.04/27.22  tff('#skF_3', type, '#skF_3': $i > $i).
% 37.04/27.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.04/27.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 37.04/27.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 37.04/27.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 37.04/27.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 37.04/27.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 37.04/27.22  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 37.04/27.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 37.04/27.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 37.04/27.22  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 37.04/27.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 37.04/27.22  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 37.04/27.22  
% 37.20/27.24  tff(f_192, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 37.20/27.24  tff(f_46, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 37.20/27.24  tff(f_48, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 37.20/27.24  tff(f_163, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tex_2)).
% 37.20/27.24  tff(f_129, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 37.20/27.24  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 37.20/27.24  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 37.20/27.24  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 37.20/27.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 37.20/27.24  tff(f_70, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 37.20/27.24  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 37.20/27.24  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_connsp_1)).
% 37.20/27.24  tff(f_55, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 37.20/27.24  tff(f_177, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 37.20/27.24  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 37.20/27.24  tff(f_108, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 37.20/27.24  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 37.20/27.24  tff(f_149, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 37.20/27.24  tff(c_76, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 37.20/27.24  tff(c_70, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 37.20/27.24  tff(c_72, plain, (v1_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 37.20/27.24  tff(c_16, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 37.20/27.24  tff(c_18, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 37.20/27.24  tff(c_77, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 37.20/27.24  tff(c_58, plain, (![A_48]: (v2_tex_2(u1_struct_0(A_48), A_48) | ~v1_tdlat_3(A_48) | ~m1_subset_1(u1_struct_0(A_48), k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_163])).
% 37.20/27.24  tff(c_81, plain, (![A_48]: (v2_tex_2(u1_struct_0(A_48), A_48) | ~v1_tdlat_3(A_48) | ~l1_pre_topc(A_48) | v2_struct_0(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_58])).
% 37.20/27.24  tff(c_66, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 37.20/27.24  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 37.20/27.24  tff(c_2599, plain, (![A_244, B_245]: (v1_pre_topc('#skF_4'(A_244, B_245)) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_244))) | v1_xboole_0(B_245) | ~l1_pre_topc(A_244) | v2_struct_0(A_244))), inference(cnfTransformation, [status(thm)], [f_129])).
% 37.20/27.24  tff(c_2627, plain, (v1_pre_topc('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_2599])).
% 37.20/27.24  tff(c_2648, plain, (v1_pre_topc('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2627])).
% 37.20/27.24  tff(c_2649, plain, (v1_pre_topc('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_2648])).
% 37.20/27.24  tff(c_2652, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_2649])).
% 37.20/27.24  tff(c_1181, plain, (![A_157, B_158, C_159]: (k9_subset_1(A_157, B_158, C_159)=k3_xboole_0(B_158, C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(A_157)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 37.20/27.24  tff(c_1211, plain, (![A_12, B_158]: (k9_subset_1(A_12, B_158, A_12)=k3_xboole_0(B_158, A_12))), inference(resolution, [status(thm)], [c_77, c_1181])).
% 37.20/27.24  tff(c_1502, plain, (![A_177, B_178, C_179]: (m1_subset_1(k9_subset_1(A_177, B_178, C_179), k1_zfmisc_1(A_177)) | ~m1_subset_1(C_179, k1_zfmisc_1(A_177)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 37.20/27.24  tff(c_1518, plain, (![B_158, A_12]: (m1_subset_1(k3_xboole_0(B_158, A_12), k1_zfmisc_1(A_12)) | ~m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_1211, c_1502])).
% 37.20/27.24  tff(c_1526, plain, (![B_180, A_181]: (m1_subset_1(k3_xboole_0(B_180, A_181), k1_zfmisc_1(A_181)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1518])).
% 37.20/27.24  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 37.20/27.24  tff(c_1537, plain, (![B_182, A_183]: (r1_tarski(k3_xboole_0(B_182, A_183), A_183))), inference(resolution, [status(thm)], [c_1526, c_26])).
% 37.20/27.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 37.20/27.24  tff(c_149, plain, (![C_78, B_79, A_80]: (~v1_xboole_0(C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_70])).
% 37.20/27.24  tff(c_166, plain, (![A_81, A_82]: (~v1_xboole_0(A_81) | ~r2_hidden(A_82, A_81))), inference(resolution, [status(thm)], [c_77, c_149])).
% 37.20/27.24  tff(c_184, plain, (![A_86, B_87]: (~v1_xboole_0(A_86) | r1_tarski(A_86, B_87))), inference(resolution, [status(thm)], [c_6, c_166])).
% 37.20/27.24  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 37.20/27.24  tff(c_194, plain, (![B_87, A_86]: (B_87=A_86 | ~r1_tarski(B_87, A_86) | ~v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_184, c_8])).
% 37.20/27.24  tff(c_1572, plain, (![B_182, A_183]: (k3_xboole_0(B_182, A_183)=A_183 | ~v1_xboole_0(A_183))), inference(resolution, [status(thm)], [c_1537, c_194])).
% 37.20/27.24  tff(c_2672, plain, (![B_182]: (k3_xboole_0(B_182, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_2652, c_1572])).
% 37.20/27.24  tff(c_32, plain, (![A_26]: (v1_xboole_0('#skF_3'(A_26)) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 37.20/27.24  tff(c_22, plain, (![A_16]: (m1_subset_1('#skF_2'(A_16), A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 37.20/27.24  tff(c_202, plain, (![C_89, A_90]: (~v1_xboole_0(C_89) | ~r2_hidden(A_90, '#skF_2'(k1_zfmisc_1(C_89))))), inference(resolution, [status(thm)], [c_22, c_149])).
% 37.20/27.24  tff(c_207, plain, (![C_89, B_2]: (~v1_xboole_0(C_89) | r1_tarski('#skF_2'(k1_zfmisc_1(C_89)), B_2))), inference(resolution, [status(thm)], [c_6, c_202])).
% 37.20/27.24  tff(c_215, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~v1_xboole_0(A_94))), inference(resolution, [status(thm)], [c_184, c_8])).
% 37.20/27.24  tff(c_429, plain, (![B_115, C_116]: (B_115='#skF_2'(k1_zfmisc_1(C_116)) | ~v1_xboole_0(B_115) | ~v1_xboole_0(C_116))), inference(resolution, [status(thm)], [c_207, c_215])).
% 37.20/27.24  tff(c_660, plain, (![A_134, C_135]: ('#skF_3'(A_134)='#skF_2'(k1_zfmisc_1(C_135)) | ~v1_xboole_0(C_135) | ~l1_pre_topc(A_134))), inference(resolution, [status(thm)], [c_32, c_429])).
% 37.20/27.24  tff(c_664, plain, (![C_136]: ('#skF_2'(k1_zfmisc_1(C_136))='#skF_3'('#skF_5') | ~v1_xboole_0(C_136))), inference(resolution, [status(thm)], [c_70, c_660])).
% 37.20/27.24  tff(c_98, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~m1_subset_1(A_67, k1_zfmisc_1(B_68)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 37.20/27.24  tff(c_116, plain, (![B_68]: (r1_tarski('#skF_2'(k1_zfmisc_1(B_68)), B_68))), inference(resolution, [status(thm)], [c_22, c_98])).
% 37.20/27.24  tff(c_733, plain, (![C_137]: (r1_tarski('#skF_3'('#skF_5'), C_137) | ~v1_xboole_0(C_137))), inference(superposition, [status(thm), theory('equality')], [c_664, c_116])).
% 37.20/27.24  tff(c_757, plain, (![C_137]: (C_137='#skF_3'('#skF_5') | ~v1_xboole_0(C_137))), inference(resolution, [status(thm)], [c_733, c_194])).
% 37.20/27.24  tff(c_2674, plain, ('#skF_3'('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_2652, c_757])).
% 37.20/27.24  tff(c_34, plain, (![A_26]: (m1_subset_1('#skF_3'(A_26), k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 37.20/27.24  tff(c_10314, plain, (![A_442, B_443]: (k9_subset_1(u1_struct_0(A_442), B_443, '#skF_3'(A_442))=k3_xboole_0(B_443, '#skF_3'(A_442)) | ~l1_pre_topc(A_442))), inference(resolution, [status(thm)], [c_34, c_1181])).
% 37.20/27.24  tff(c_64, plain, (![B_55, A_51, C_57]: (~v2_tex_2(B_55, A_51) | v2_tex_2(k9_subset_1(u1_struct_0(A_51), B_55, C_57), A_51) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_177])).
% 37.20/27.24  tff(c_153349, plain, (![B_1698, A_1699]: (~v2_tex_2(B_1698, A_1699) | v2_tex_2(k3_xboole_0(B_1698, '#skF_3'(A_1699)), A_1699) | ~m1_subset_1('#skF_3'(A_1699), k1_zfmisc_1(u1_struct_0(A_1699))) | ~m1_subset_1(B_1698, k1_zfmisc_1(u1_struct_0(A_1699))) | ~l1_pre_topc(A_1699) | ~l1_pre_topc(A_1699))), inference(superposition, [status(thm), theory('equality')], [c_10314, c_64])).
% 37.20/27.24  tff(c_153379, plain, (![B_1698]: (~v2_tex_2(B_1698, '#skF_5') | v2_tex_2(k3_xboole_0(B_1698, '#skF_3'('#skF_5')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_1698, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2674, c_153349])).
% 37.20/27.24  tff(c_153388, plain, (![B_1698]: (~v2_tex_2(B_1698, '#skF_5') | v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1(B_1698, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_68, c_2672, c_2674, c_153379])).
% 37.20/27.24  tff(c_153392, plain, (![B_1700]: (~v2_tex_2(B_1700, '#skF_5') | ~m1_subset_1(B_1700, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_153388])).
% 37.20/27.24  tff(c_153543, plain, (~v2_tex_2(u1_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_77, c_153392])).
% 37.20/27.24  tff(c_153550, plain, (~v1_tdlat_3('#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_81, c_153543])).
% 37.20/27.24  tff(c_153557, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_153550])).
% 37.20/27.24  tff(c_153559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_153557])).
% 37.20/27.24  tff(c_153561, plain, (~v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_2649])).
% 37.20/27.24  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 37.20/27.24  tff(c_113, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_98])).
% 37.20/27.24  tff(c_171, plain, (![A_83, C_84, B_85]: (r1_tarski(A_83, C_84) | ~r1_tarski(B_85, C_84) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_44])).
% 37.20/27.24  tff(c_182, plain, (![A_83]: (r1_tarski(A_83, u1_struct_0('#skF_5')) | ~r1_tarski(A_83, '#skF_6'))), inference(resolution, [status(thm)], [c_113, c_171])).
% 37.20/27.24  tff(c_28, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 37.20/27.24  tff(c_154395, plain, (![A_1732, B_1733]: (m1_pre_topc('#skF_4'(A_1732, B_1733), A_1732) | ~m1_subset_1(B_1733, k1_zfmisc_1(u1_struct_0(A_1732))) | v1_xboole_0(B_1733) | ~l1_pre_topc(A_1732) | v2_struct_0(A_1732))), inference(cnfTransformation, [status(thm)], [f_129])).
% 37.20/27.24  tff(c_169609, plain, (![A_2029, A_2030]: (m1_pre_topc('#skF_4'(A_2029, A_2030), A_2029) | v1_xboole_0(A_2030) | ~l1_pre_topc(A_2029) | v2_struct_0(A_2029) | ~r1_tarski(A_2030, u1_struct_0(A_2029)))), inference(resolution, [status(thm)], [c_28, c_154395])).
% 37.20/27.24  tff(c_169753, plain, (![A_83]: (m1_pre_topc('#skF_4'('#skF_5', A_83), '#skF_5') | v1_xboole_0(A_83) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(A_83, '#skF_6'))), inference(resolution, [status(thm)], [c_182, c_169609])).
% 37.20/27.24  tff(c_169866, plain, (![A_83]: (m1_pre_topc('#skF_4'('#skF_5', A_83), '#skF_5') | v1_xboole_0(A_83) | v2_struct_0('#skF_5') | ~r1_tarski(A_83, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_169753])).
% 37.20/27.24  tff(c_169867, plain, (![A_83]: (m1_pre_topc('#skF_4'('#skF_5', A_83), '#skF_5') | v1_xboole_0(A_83) | ~r1_tarski(A_83, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_169866])).
% 37.20/27.24  tff(c_153811, plain, (![A_1709, B_1710]: (~v2_struct_0('#skF_4'(A_1709, B_1710)) | ~m1_subset_1(B_1710, k1_zfmisc_1(u1_struct_0(A_1709))) | v1_xboole_0(B_1710) | ~l1_pre_topc(A_1709) | v2_struct_0(A_1709))), inference(cnfTransformation, [status(thm)], [f_129])).
% 37.20/27.24  tff(c_153839, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_153811])).
% 37.20/27.24  tff(c_153860, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_153839])).
% 37.20/27.24  tff(c_153861, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_153561, c_153860])).
% 37.20/27.24  tff(c_74, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 37.20/27.24  tff(c_154415, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_154395])).
% 37.20/27.24  tff(c_154434, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_154415])).
% 37.20/27.24  tff(c_154435, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_76, c_153561, c_154434])).
% 37.20/27.24  tff(c_40, plain, (![B_34, A_32]: (v1_tdlat_3(B_34) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32) | ~v1_tdlat_3(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_108])).
% 37.20/27.24  tff(c_154440, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v1_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_154435, c_40])).
% 37.20/27.24  tff(c_154443, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_154440])).
% 37.20/27.24  tff(c_154444, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_154443])).
% 37.20/27.24  tff(c_155014, plain, (![A_1748, B_1749]: (u1_struct_0('#skF_4'(A_1748, B_1749))=B_1749 | ~m1_subset_1(B_1749, k1_zfmisc_1(u1_struct_0(A_1748))) | v1_xboole_0(B_1749) | ~l1_pre_topc(A_1748) | v2_struct_0(A_1748))), inference(cnfTransformation, [status(thm)], [f_129])).
% 37.20/27.24  tff(c_155042, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_155014])).
% 37.20/27.24  tff(c_155063, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_155042])).
% 37.20/27.24  tff(c_155064, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_76, c_153561, c_155063])).
% 37.20/27.24  tff(c_36, plain, (![B_30, A_28]: (m1_subset_1(u1_struct_0(B_30), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_84])).
% 37.20/27.24  tff(c_155503, plain, (![B_1758, A_1759]: (v2_tex_2(u1_struct_0(B_1758), A_1759) | ~v1_tdlat_3(B_1758) | ~m1_subset_1(u1_struct_0(B_1758), k1_zfmisc_1(u1_struct_0(A_1759))) | ~m1_pre_topc(B_1758, A_1759) | v2_struct_0(B_1758) | ~l1_pre_topc(A_1759) | v2_struct_0(A_1759))), inference(cnfTransformation, [status(thm)], [f_149])).
% 37.20/27.24  tff(c_171775, plain, (![B_2066, A_2067]: (v2_tex_2(u1_struct_0(B_2066), A_2067) | ~v1_tdlat_3(B_2066) | v2_struct_0(B_2066) | v2_struct_0(A_2067) | ~m1_pre_topc(B_2066, A_2067) | ~l1_pre_topc(A_2067))), inference(resolution, [status(thm)], [c_36, c_155503])).
% 37.20/27.24  tff(c_171791, plain, (![A_2067]: (v2_tex_2('#skF_6', A_2067) | ~v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0(A_2067) | ~m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), A_2067) | ~l1_pre_topc(A_2067))), inference(superposition, [status(thm), theory('equality')], [c_155064, c_171775])).
% 37.20/27.24  tff(c_171795, plain, (![A_2067]: (v2_tex_2('#skF_6', A_2067) | v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0(A_2067) | ~m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), A_2067) | ~l1_pre_topc(A_2067))), inference(demodulation, [status(thm), theory('equality')], [c_154444, c_171791])).
% 37.20/27.24  tff(c_188345, plain, (![A_2286]: (v2_tex_2('#skF_6', A_2286) | v2_struct_0(A_2286) | ~m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), A_2286) | ~l1_pre_topc(A_2286))), inference(negUnitSimplification, [status(thm)], [c_153861, c_171795])).
% 37.20/27.24  tff(c_188349, plain, (v2_tex_2('#skF_6', '#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5') | v1_xboole_0('#skF_6') | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_169867, c_188345])).
% 37.20/27.24  tff(c_188355, plain, (v2_tex_2('#skF_6', '#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_70, c_188349])).
% 37.20/27.24  tff(c_188357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_153561, c_76, c_66, c_188355])).
% 37.20/27.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 37.20/27.24  
% 37.20/27.24  Inference rules
% 37.20/27.24  ----------------------
% 37.20/27.24  #Ref     : 0
% 37.20/27.24  #Sup     : 53217
% 37.20/27.24  #Fact    : 0
% 37.20/27.24  #Define  : 0
% 37.20/27.24  #Split   : 17
% 37.20/27.24  #Chain   : 0
% 37.20/27.24  #Close   : 0
% 37.20/27.24  
% 37.20/27.24  Ordering : KBO
% 37.20/27.24  
% 37.20/27.24  Simplification rules
% 37.20/27.24  ----------------------
% 37.20/27.24  #Subsume      : 26221
% 37.20/27.24  #Demod        : 26876
% 37.20/27.24  #Tautology    : 10395
% 37.20/27.24  #SimpNegUnit  : 200
% 37.20/27.24  #BackRed      : 32
% 37.20/27.24  
% 37.20/27.24  #Partial instantiations: 0
% 37.20/27.24  #Strategies tried      : 1
% 37.20/27.24  
% 37.20/27.24  Timing (in seconds)
% 37.20/27.24  ----------------------
% 37.20/27.25  Preprocessing        : 0.34
% 37.20/27.25  Parsing              : 0.17
% 37.20/27.25  CNF conversion       : 0.03
% 37.20/27.25  Main loop            : 26.14
% 37.20/27.25  Inferencing          : 3.77
% 37.20/27.25  Reduction            : 7.72
% 37.20/27.25  Demodulation         : 5.91
% 37.20/27.25  BG Simplification    : 0.40
% 37.20/27.25  Subsumption          : 12.77
% 37.20/27.25  Abstraction          : 0.76
% 37.20/27.25  MUC search           : 0.00
% 37.20/27.25  Cooper               : 0.00
% 37.20/27.25  Total                : 26.53
% 37.20/27.25  Index Insertion      : 0.00
% 37.20/27.25  Index Deletion       : 0.00
% 37.20/27.25  Index Matching       : 0.00
% 37.20/27.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
