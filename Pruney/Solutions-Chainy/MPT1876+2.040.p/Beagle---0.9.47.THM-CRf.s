%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:56 EST 2020

% Result     : Theorem 7.18s
% Output     : CNFRefutation 7.18s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 897 expanded)
%              Number of leaves         :   42 ( 323 expanded)
%              Depth                    :   32
%              Number of atoms          :  479 (3037 expanded)
%              Number of equality atoms :   18 (  46 expanded)
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

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_193,negated_conjecture,(
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

tff(f_161,axiom,(
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

tff(f_132,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_173,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_119,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(c_26,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_74,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_77,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_80,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_68])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_160,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden('#skF_2'(A_67,B_68),B_68)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_170,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_160])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_111,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_124,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_111])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172,plain,(
    ! [C_70,B_71,A_72] :
      ( r2_hidden(C_70,B_71)
      | ~ r2_hidden(C_70,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_184,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_1'(A_76),B_77)
      | ~ r1_tarski(A_76,B_77)
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_4,c_172])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_196,plain,(
    ! [B_78,A_79] :
      ( ~ v1_xboole_0(B_78)
      | ~ r1_tarski(A_79,B_78)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_184,c_2])).

tff(c_208,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_124,c_196])).

tff(c_214,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_208])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( m1_subset_1(B_12,A_11)
      | ~ r2_hidden(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_194,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1('#skF_1'(A_76),B_77)
      | v1_xboole_0(B_77)
      | ~ r1_tarski(A_76,B_77)
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_184,c_14])).

tff(c_12,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_137,plain,(
    ! [B_64,A_65] :
      ( m1_subset_1(B_64,A_65)
      | ~ r2_hidden(B_64,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_149,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_137])).

tff(c_215,plain,(
    ! [A_80,B_81] :
      ( k6_domain_1(A_80,B_81) = k1_tarski(B_81)
      | ~ m1_subset_1(B_81,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_228,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = k1_tarski('#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_149,c_215])).

tff(c_274,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1(k6_domain_1(A_86,B_87),k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4684,plain,(
    ! [A_259] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_259)),k1_zfmisc_1(A_259))
      | ~ m1_subset_1('#skF_1'(A_259),A_259)
      | v1_xboole_0(A_259)
      | v1_xboole_0(A_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_274])).

tff(c_96,plain,(
    ! [B_52,A_53] :
      ( v1_xboole_0(B_52)
      | ~ m1_subset_1(B_52,A_53)
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_105,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_56,c_96])).

tff(c_110,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_105])).

tff(c_351,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1('#skF_2'(A_92,B_93),A_92)
      | v1_xboole_0(A_92)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1504,plain,(
    ! [B_165,B_166] :
      ( r1_tarski('#skF_2'(k1_zfmisc_1(B_165),B_166),B_165)
      | v1_xboole_0(k1_zfmisc_1(B_165))
      | r1_tarski(k1_zfmisc_1(B_165),B_166) ) ),
    inference(resolution,[status(thm)],[c_351,c_22])).

tff(c_371,plain,(
    ! [A_94,B_95,B_96] :
      ( r2_hidden('#skF_2'(A_94,B_95),B_96)
      | ~ r1_tarski(A_94,B_96)
      | r1_tarski(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_10,c_172])).

tff(c_1206,plain,(
    ! [A_152,B_153,B_154] :
      ( m1_subset_1('#skF_2'(A_152,B_153),B_154)
      | v1_xboole_0(B_154)
      | ~ r1_tarski(A_152,B_154)
      | r1_tarski(A_152,B_153) ) ),
    inference(resolution,[status(thm)],[c_371,c_14])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_424,plain,(
    ! [B_104,B_105,A_106] :
      ( r2_hidden(B_104,B_105)
      | ~ r1_tarski(A_106,B_105)
      | ~ m1_subset_1(B_104,A_106)
      | v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_16,c_172])).

tff(c_438,plain,(
    ! [B_104] :
      ( r2_hidden(B_104,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_104,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_124,c_424])).

tff(c_450,plain,(
    ! [B_107] :
      ( r2_hidden(B_107,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_107,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_438])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_464,plain,(
    ! [A_5] :
      ( r1_tarski(A_5,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_5,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_450,c_8])).

tff(c_1226,plain,(
    ! [A_152] :
      ( v1_xboole_0('#skF_5')
      | ~ r1_tarski(A_152,'#skF_5')
      | r1_tarski(A_152,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1206,c_464])).

tff(c_1313,plain,(
    ! [A_157] :
      ( ~ r1_tarski(A_157,'#skF_5')
      | r1_tarski(A_157,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1226])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_322,plain,(
    ! [A_88,A_89] :
      ( r1_tarski(A_88,A_89)
      | ~ m1_subset_1('#skF_2'(A_88,A_89),A_89)
      | v1_xboole_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_16,c_160])).

tff(c_331,plain,(
    ! [A_88,B_14] :
      ( r1_tarski(A_88,k1_zfmisc_1(B_14))
      | v1_xboole_0(k1_zfmisc_1(B_14))
      | ~ r1_tarski('#skF_2'(A_88,k1_zfmisc_1(B_14)),B_14) ) ),
    inference(resolution,[status(thm)],[c_24,c_322])).

tff(c_1317,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'(A_88,k1_zfmisc_1(u1_struct_0('#skF_4'))),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1313,c_331])).

tff(c_1338,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'(A_88,k1_zfmisc_1(u1_struct_0('#skF_4'))),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_1317])).

tff(c_1525,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_5'))
    | r1_tarski(k1_zfmisc_1('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_1504,c_1338])).

tff(c_1533,plain,(
    r1_tarski(k1_zfmisc_1('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1525])).

tff(c_179,plain,(
    ! [B_12,B_71,A_11] :
      ( r2_hidden(B_12,B_71)
      | ~ r1_tarski(A_11,B_71)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_172])).

tff(c_1547,plain,(
    ! [B_12] :
      ( r2_hidden(B_12,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_12,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1533,c_179])).

tff(c_1600,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1547])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( v1_xboole_0(B_12)
      | ~ m1_subset_1(B_12,A_11)
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_766,plain,(
    ! [A_125,B_126] :
      ( v1_xboole_0(k6_domain_1(A_125,B_126))
      | ~ v1_xboole_0(k1_zfmisc_1(A_125))
      | ~ m1_subset_1(B_126,A_125)
      | v1_xboole_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_274,c_20])).

tff(c_781,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_tarski('#skF_1'(A_1)))
      | ~ v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_766])).

tff(c_838,plain,(
    ! [A_129] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_129))
      | ~ m1_subset_1('#skF_1'(A_129),A_129)
      | v1_xboole_0(A_129)
      | v1_xboole_0(A_129) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_781])).

tff(c_842,plain,(
    ! [B_77] :
      ( ~ v1_xboole_0(k1_zfmisc_1(B_77))
      | ~ r1_tarski(B_77,B_77)
      | v1_xboole_0(B_77) ) ),
    inference(resolution,[status(thm)],[c_194,c_838])).

tff(c_864,plain,(
    ! [B_77] :
      ( ~ v1_xboole_0(k1_zfmisc_1(B_77))
      | v1_xboole_0(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_842])).

tff(c_1603,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1600,c_864])).

tff(c_1609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1603])).

tff(c_1616,plain,(
    ! [B_169] :
      ( r2_hidden(B_169,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_169,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_1547])).

tff(c_1625,plain,(
    ! [B_169] :
      ( m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_169,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1616,c_14])).

tff(c_1733,plain,(
    ! [B_173] :
      ( m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_173,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_1625])).

tff(c_48,plain,(
    ! [A_31,B_35] :
      ( v1_tdlat_3('#skF_3'(A_31,B_35))
      | ~ v2_tex_2(B_35,A_31)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_31)))
      | v1_xboole_0(B_35)
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1743,plain,(
    ! [B_173] :
      ( v1_tdlat_3('#skF_3'('#skF_4',B_173))
      | ~ v2_tex_2(B_173,'#skF_4')
      | v1_xboole_0(B_173)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_173,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1733,c_48])).

tff(c_1775,plain,(
    ! [B_173] :
      ( v1_tdlat_3('#skF_3'('#skF_4',B_173))
      | ~ v2_tex_2(B_173,'#skF_4')
      | v1_xboole_0(B_173)
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_173,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1743])).

tff(c_1776,plain,(
    ! [B_173] :
      ( v1_tdlat_3('#skF_3'('#skF_4',B_173))
      | ~ v2_tex_2(B_173,'#skF_4')
      | v1_xboole_0(B_173)
      | ~ m1_subset_1(B_173,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1775])).

tff(c_4708,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4684,c_1776])).

tff(c_4758,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_58,c_12,c_4708])).

tff(c_4956,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4758])).

tff(c_4959,plain,
    ( ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_194,c_4956])).

tff(c_4968,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_4959])).

tff(c_4970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4968])).

tff(c_4972,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_4758])).

tff(c_1342,plain,(
    ! [B_12,A_157] :
      ( r2_hidden(B_12,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_12,A_157)
      | v1_xboole_0(A_157)
      | ~ r1_tarski(A_157,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1313,c_179])).

tff(c_4978,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_4972,c_1342])).

tff(c_4993,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_4978])).

tff(c_4994,plain,(
    r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4993])).

tff(c_5003,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4994,c_14])).

tff(c_5010,plain,(
    m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_5003])).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4981,plain,
    ( k6_domain_1('#skF_5','#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4972,c_34])).

tff(c_4997,plain,(
    k6_domain_1('#skF_5','#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4981])).

tff(c_291,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k6_domain_1(A_86,B_87),A_86)
      | ~ m1_subset_1(B_87,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_274,c_22])).

tff(c_5046,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),'#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4997,c_291])).

tff(c_5069,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4972,c_5046])).

tff(c_5070,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_5')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5069])).

tff(c_42,plain,(
    ! [B_30,A_28] :
      ( B_30 = A_28
      | ~ r1_tarski(A_28,B_30)
      | ~ v1_zfmisc_1(B_30)
      | v1_xboole_0(B_30)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5201,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_5070,c_42])).

tff(c_5222,plain,
    ( k1_tarski('#skF_1'('#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_5201])).

tff(c_5223,plain,(
    k1_tarski('#skF_1'('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_58,c_5222])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_973,plain,(
    ! [A_134,B_135,B_136] :
      ( r2_hidden('#skF_1'(A_134),B_135)
      | ~ r1_tarski(B_136,B_135)
      | ~ r1_tarski(A_134,B_136)
      | v1_xboole_0(A_134) ) ),
    inference(resolution,[status(thm)],[c_184,c_6])).

tff(c_998,plain,(
    ! [A_137] :
      ( r2_hidden('#skF_1'(A_137),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_137,'#skF_5')
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_124,c_973])).

tff(c_1003,plain,(
    ! [A_137] :
      ( m1_subset_1('#skF_1'(A_137),u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_137,'#skF_5')
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_998,c_14])).

tff(c_1012,plain,(
    ! [A_138] :
      ( m1_subset_1('#skF_1'(A_138),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_138,'#skF_5')
      | v1_xboole_0(A_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1003])).

tff(c_1015,plain,(
    ! [A_138] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_138)) = k1_tarski('#skF_1'(A_138))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_138,'#skF_5')
      | v1_xboole_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_1012,c_34])).

tff(c_2930,plain,(
    ! [A_206] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_206)) = k1_tarski('#skF_1'(A_206))
      | ~ r1_tarski(A_206,'#skF_5')
      | v1_xboole_0(A_206) ) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1015])).

tff(c_54,plain,(
    ! [A_37,B_39] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_37),B_39),A_37)
      | ~ m1_subset_1(B_39,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_2942,plain,(
    ! [A_206] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_206)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_206),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_206,'#skF_5')
      | v1_xboole_0(A_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2930,c_54])).

tff(c_2967,plain,(
    ! [A_206] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_206)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_206),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_206,'#skF_5')
      | v1_xboole_0(A_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2942])).

tff(c_2968,plain,(
    ! [A_206] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_206)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_206),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_206,'#skF_5')
      | v1_xboole_0(A_206) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2967])).

tff(c_5241,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5223,c_2968])).

tff(c_5276,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_5010,c_5241])).

tff(c_5278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_80,c_5276])).

tff(c_5279,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_6107,plain,(
    ! [A_360,B_361] :
      ( ~ v2_struct_0('#skF_3'(A_360,B_361))
      | ~ v2_tex_2(B_361,A_360)
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0(A_360)))
      | v1_xboole_0(B_361)
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_6137,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6107])).

tff(c_6150,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_5279,c_6137])).

tff(c_6151,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_6150])).

tff(c_5280,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_6630,plain,(
    ! [A_383,B_384] :
      ( u1_struct_0('#skF_3'(A_383,B_384)) = B_384
      | ~ v2_tex_2(B_384,A_383)
      | ~ m1_subset_1(B_384,k1_zfmisc_1(u1_struct_0(A_383)))
      | v1_xboole_0(B_384)
      | ~ l1_pre_topc(A_383)
      | ~ v2_pre_topc(A_383)
      | v2_struct_0(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_6663,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6630])).

tff(c_6680,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_5279,c_6663])).

tff(c_6681,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_6680])).

tff(c_30,plain,(
    ! [A_19] :
      ( v1_zfmisc_1(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | ~ v7_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6700,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6681,c_30])).

tff(c_6709,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_5280,c_6700])).

tff(c_6711,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6709])).

tff(c_62,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_6439,plain,(
    ! [A_373,B_374] :
      ( v1_tdlat_3('#skF_3'(A_373,B_374))
      | ~ v2_tex_2(B_374,A_373)
      | ~ m1_subset_1(B_374,k1_zfmisc_1(u1_struct_0(A_373)))
      | v1_xboole_0(B_374)
      | ~ l1_pre_topc(A_373)
      | ~ v2_pre_topc(A_373)
      | v2_struct_0(A_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_6469,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6439])).

tff(c_6482,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_5279,c_6469])).

tff(c_6483,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_6482])).

tff(c_6785,plain,(
    ! [A_392,B_393] :
      ( m1_pre_topc('#skF_3'(A_392,B_393),A_392)
      | ~ v2_tex_2(B_393,A_392)
      | ~ m1_subset_1(B_393,k1_zfmisc_1(u1_struct_0(A_392)))
      | v1_xboole_0(B_393)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_6811,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6785])).

tff(c_6829,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_5279,c_6811])).

tff(c_6830,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_6829])).

tff(c_38,plain,(
    ! [B_27,A_25] :
      ( ~ v1_tdlat_3(B_27)
      | v7_struct_0(B_27)
      | v2_struct_0(B_27)
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6833,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6830,c_38])).

tff(c_6839,plain,
    ( v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_6483,c_6833])).

tff(c_6841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6151,c_6711,c_6839])).

tff(c_6842,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6709])).

tff(c_6847,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_26,c_6842])).

tff(c_6897,plain,(
    ! [A_399,B_400] :
      ( m1_pre_topc('#skF_3'(A_399,B_400),A_399)
      | ~ v2_tex_2(B_400,A_399)
      | ~ m1_subset_1(B_400,k1_zfmisc_1(u1_struct_0(A_399)))
      | v1_xboole_0(B_400)
      | ~ l1_pre_topc(A_399)
      | ~ v2_pre_topc(A_399)
      | v2_struct_0(A_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_6923,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_6897])).

tff(c_6941,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_5279,c_6923])).

tff(c_6942,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_6941])).

tff(c_28,plain,(
    ! [B_18,A_16] :
      ( l1_pre_topc(B_18)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6948,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6942,c_28])).

tff(c_6955,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6948])).

tff(c_6957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6847,c_6955])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:49:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.18/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.48  
% 7.18/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.48  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 7.18/2.48  
% 7.18/2.48  %Foreground sorts:
% 7.18/2.48  
% 7.18/2.48  
% 7.18/2.48  %Background operators:
% 7.18/2.48  
% 7.18/2.48  
% 7.18/2.48  %Foreground operators:
% 7.18/2.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.18/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.18/2.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.18/2.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.18/2.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.18/2.48  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 7.18/2.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.18/2.48  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.18/2.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.18/2.48  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 7.18/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.18/2.48  tff('#skF_5', type, '#skF_5': $i).
% 7.18/2.48  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.18/2.48  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.18/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.18/2.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.18/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.18/2.48  tff('#skF_4', type, '#skF_4': $i).
% 7.18/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.18/2.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.18/2.48  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 7.18/2.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.18/2.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.18/2.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.18/2.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.18/2.48  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 7.18/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.18/2.48  
% 7.18/2.51  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.18/2.51  tff(f_193, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 7.18/2.51  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.18/2.51  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.18/2.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.18/2.51  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 7.18/2.51  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 7.18/2.51  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 7.18/2.51  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 7.18/2.51  tff(f_161, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 7.18/2.51  tff(f_132, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 7.18/2.51  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 7.18/2.51  tff(f_75, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 7.18/2.51  tff(f_119, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 7.18/2.51  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.18/2.51  tff(c_26, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.18/2.51  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.18/2.51  tff(c_58, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.18/2.51  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.18/2.51  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.18/2.51  tff(c_74, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.18/2.51  tff(c_77, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 7.18/2.51  tff(c_68, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.18/2.51  tff(c_80, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_68])).
% 7.18/2.51  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.18/2.51  tff(c_160, plain, (![A_67, B_68]: (~r2_hidden('#skF_2'(A_67, B_68), B_68) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.18/2.51  tff(c_170, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_160])).
% 7.18/2.51  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.18/2.51  tff(c_111, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.18/2.51  tff(c_124, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_111])).
% 7.18/2.51  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.18/2.51  tff(c_172, plain, (![C_70, B_71, A_72]: (r2_hidden(C_70, B_71) | ~r2_hidden(C_70, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.18/2.51  tff(c_184, plain, (![A_76, B_77]: (r2_hidden('#skF_1'(A_76), B_77) | ~r1_tarski(A_76, B_77) | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_4, c_172])).
% 7.18/2.51  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.18/2.51  tff(c_196, plain, (![B_78, A_79]: (~v1_xboole_0(B_78) | ~r1_tarski(A_79, B_78) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_184, c_2])).
% 7.18/2.51  tff(c_208, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_124, c_196])).
% 7.18/2.51  tff(c_214, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_208])).
% 7.18/2.51  tff(c_14, plain, (![B_12, A_11]: (m1_subset_1(B_12, A_11) | ~r2_hidden(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.18/2.51  tff(c_194, plain, (![A_76, B_77]: (m1_subset_1('#skF_1'(A_76), B_77) | v1_xboole_0(B_77) | ~r1_tarski(A_76, B_77) | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_184, c_14])).
% 7.18/2.51  tff(c_12, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.18/2.51  tff(c_137, plain, (![B_64, A_65]: (m1_subset_1(B_64, A_65) | ~r2_hidden(B_64, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.18/2.51  tff(c_149, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_137])).
% 7.18/2.51  tff(c_215, plain, (![A_80, B_81]: (k6_domain_1(A_80, B_81)=k1_tarski(B_81) | ~m1_subset_1(B_81, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.18/2.51  tff(c_228, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=k1_tarski('#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_149, c_215])).
% 7.18/2.51  tff(c_274, plain, (![A_86, B_87]: (m1_subset_1(k6_domain_1(A_86, B_87), k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.18/2.51  tff(c_4684, plain, (![A_259]: (m1_subset_1(k1_tarski('#skF_1'(A_259)), k1_zfmisc_1(A_259)) | ~m1_subset_1('#skF_1'(A_259), A_259) | v1_xboole_0(A_259) | v1_xboole_0(A_259))), inference(superposition, [status(thm), theory('equality')], [c_228, c_274])).
% 7.18/2.51  tff(c_96, plain, (![B_52, A_53]: (v1_xboole_0(B_52) | ~m1_subset_1(B_52, A_53) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.18/2.51  tff(c_105, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_56, c_96])).
% 7.18/2.51  tff(c_110, plain, (~v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_105])).
% 7.18/2.51  tff(c_351, plain, (![A_92, B_93]: (m1_subset_1('#skF_2'(A_92, B_93), A_92) | v1_xboole_0(A_92) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_10, c_137])).
% 7.18/2.51  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.18/2.51  tff(c_1504, plain, (![B_165, B_166]: (r1_tarski('#skF_2'(k1_zfmisc_1(B_165), B_166), B_165) | v1_xboole_0(k1_zfmisc_1(B_165)) | r1_tarski(k1_zfmisc_1(B_165), B_166))), inference(resolution, [status(thm)], [c_351, c_22])).
% 7.18/2.51  tff(c_371, plain, (![A_94, B_95, B_96]: (r2_hidden('#skF_2'(A_94, B_95), B_96) | ~r1_tarski(A_94, B_96) | r1_tarski(A_94, B_95))), inference(resolution, [status(thm)], [c_10, c_172])).
% 7.18/2.51  tff(c_1206, plain, (![A_152, B_153, B_154]: (m1_subset_1('#skF_2'(A_152, B_153), B_154) | v1_xboole_0(B_154) | ~r1_tarski(A_152, B_154) | r1_tarski(A_152, B_153))), inference(resolution, [status(thm)], [c_371, c_14])).
% 7.18/2.51  tff(c_16, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.18/2.51  tff(c_424, plain, (![B_104, B_105, A_106]: (r2_hidden(B_104, B_105) | ~r1_tarski(A_106, B_105) | ~m1_subset_1(B_104, A_106) | v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_16, c_172])).
% 7.18/2.51  tff(c_438, plain, (![B_104]: (r2_hidden(B_104, u1_struct_0('#skF_4')) | ~m1_subset_1(B_104, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_124, c_424])).
% 7.18/2.51  tff(c_450, plain, (![B_107]: (r2_hidden(B_107, u1_struct_0('#skF_4')) | ~m1_subset_1(B_107, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_438])).
% 7.18/2.51  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.18/2.51  tff(c_464, plain, (![A_5]: (r1_tarski(A_5, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_5, u1_struct_0('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_450, c_8])).
% 7.18/2.51  tff(c_1226, plain, (![A_152]: (v1_xboole_0('#skF_5') | ~r1_tarski(A_152, '#skF_5') | r1_tarski(A_152, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1206, c_464])).
% 7.18/2.51  tff(c_1313, plain, (![A_157]: (~r1_tarski(A_157, '#skF_5') | r1_tarski(A_157, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1226])).
% 7.18/2.51  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.18/2.51  tff(c_322, plain, (![A_88, A_89]: (r1_tarski(A_88, A_89) | ~m1_subset_1('#skF_2'(A_88, A_89), A_89) | v1_xboole_0(A_89))), inference(resolution, [status(thm)], [c_16, c_160])).
% 7.18/2.51  tff(c_331, plain, (![A_88, B_14]: (r1_tarski(A_88, k1_zfmisc_1(B_14)) | v1_xboole_0(k1_zfmisc_1(B_14)) | ~r1_tarski('#skF_2'(A_88, k1_zfmisc_1(B_14)), B_14))), inference(resolution, [status(thm)], [c_24, c_322])).
% 7.18/2.51  tff(c_1317, plain, (![A_88]: (r1_tarski(A_88, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'(A_88, k1_zfmisc_1(u1_struct_0('#skF_4'))), '#skF_5'))), inference(resolution, [status(thm)], [c_1313, c_331])).
% 7.18/2.51  tff(c_1338, plain, (![A_88]: (r1_tarski(A_88, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'(A_88, k1_zfmisc_1(u1_struct_0('#skF_4'))), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_110, c_1317])).
% 7.18/2.51  tff(c_1525, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5')) | r1_tarski(k1_zfmisc_1('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1504, c_1338])).
% 7.18/2.51  tff(c_1533, plain, (r1_tarski(k1_zfmisc_1('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_1525])).
% 7.18/2.51  tff(c_179, plain, (![B_12, B_71, A_11]: (r2_hidden(B_12, B_71) | ~r1_tarski(A_11, B_71) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_16, c_172])).
% 7.18/2.51  tff(c_1547, plain, (![B_12]: (r2_hidden(B_12, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_12, k1_zfmisc_1('#skF_5')) | v1_xboole_0(k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_1533, c_179])).
% 7.18/2.51  tff(c_1600, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1547])).
% 7.18/2.51  tff(c_20, plain, (![B_12, A_11]: (v1_xboole_0(B_12) | ~m1_subset_1(B_12, A_11) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.18/2.51  tff(c_766, plain, (![A_125, B_126]: (v1_xboole_0(k6_domain_1(A_125, B_126)) | ~v1_xboole_0(k1_zfmisc_1(A_125)) | ~m1_subset_1(B_126, A_125) | v1_xboole_0(A_125))), inference(resolution, [status(thm)], [c_274, c_20])).
% 7.18/2.51  tff(c_781, plain, (![A_1]: (v1_xboole_0(k1_tarski('#skF_1'(A_1))) | ~v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1) | v1_xboole_0(A_1))), inference(superposition, [status(thm), theory('equality')], [c_228, c_766])).
% 7.18/2.51  tff(c_838, plain, (![A_129]: (~v1_xboole_0(k1_zfmisc_1(A_129)) | ~m1_subset_1('#skF_1'(A_129), A_129) | v1_xboole_0(A_129) | v1_xboole_0(A_129))), inference(negUnitSimplification, [status(thm)], [c_12, c_781])).
% 7.18/2.51  tff(c_842, plain, (![B_77]: (~v1_xboole_0(k1_zfmisc_1(B_77)) | ~r1_tarski(B_77, B_77) | v1_xboole_0(B_77))), inference(resolution, [status(thm)], [c_194, c_838])).
% 7.18/2.51  tff(c_864, plain, (![B_77]: (~v1_xboole_0(k1_zfmisc_1(B_77)) | v1_xboole_0(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_842])).
% 7.18/2.51  tff(c_1603, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1600, c_864])).
% 7.18/2.51  tff(c_1609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1603])).
% 7.18/2.51  tff(c_1616, plain, (![B_169]: (r2_hidden(B_169, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_169, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_1547])).
% 7.18/2.51  tff(c_1625, plain, (![B_169]: (m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_169, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_1616, c_14])).
% 7.18/2.51  tff(c_1733, plain, (![B_173]: (m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_173, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_110, c_1625])).
% 7.18/2.51  tff(c_48, plain, (![A_31, B_35]: (v1_tdlat_3('#skF_3'(A_31, B_35)) | ~v2_tex_2(B_35, A_31) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_31))) | v1_xboole_0(B_35) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.18/2.51  tff(c_1743, plain, (![B_173]: (v1_tdlat_3('#skF_3'('#skF_4', B_173)) | ~v2_tex_2(B_173, '#skF_4') | v1_xboole_0(B_173) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(B_173, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_1733, c_48])).
% 7.18/2.51  tff(c_1775, plain, (![B_173]: (v1_tdlat_3('#skF_3'('#skF_4', B_173)) | ~v2_tex_2(B_173, '#skF_4') | v1_xboole_0(B_173) | v2_struct_0('#skF_4') | ~m1_subset_1(B_173, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1743])).
% 7.18/2.51  tff(c_1776, plain, (![B_173]: (v1_tdlat_3('#skF_3'('#skF_4', B_173)) | ~v2_tex_2(B_173, '#skF_4') | v1_xboole_0(B_173) | ~m1_subset_1(B_173, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1775])).
% 7.18/2.51  tff(c_4708, plain, (v1_tdlat_3('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4684, c_1776])).
% 7.18/2.51  tff(c_4758, plain, (v1_tdlat_3('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_58, c_12, c_4708])).
% 7.18/2.51  tff(c_4956, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_4758])).
% 7.18/2.51  tff(c_4959, plain, (~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_194, c_4956])).
% 7.18/2.51  tff(c_4968, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_4959])).
% 7.18/2.51  tff(c_4970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_4968])).
% 7.18/2.51  tff(c_4972, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_4758])).
% 7.18/2.51  tff(c_1342, plain, (![B_12, A_157]: (r2_hidden(B_12, u1_struct_0('#skF_4')) | ~m1_subset_1(B_12, A_157) | v1_xboole_0(A_157) | ~r1_tarski(A_157, '#skF_5'))), inference(resolution, [status(thm)], [c_1313, c_179])).
% 7.18/2.51  tff(c_4978, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5') | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_4972, c_1342])).
% 7.18/2.51  tff(c_4993, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_4978])).
% 7.18/2.51  tff(c_4994, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_4993])).
% 7.18/2.51  tff(c_5003, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4994, c_14])).
% 7.18/2.51  tff(c_5010, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_214, c_5003])).
% 7.18/2.51  tff(c_34, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.18/2.51  tff(c_4981, plain, (k6_domain_1('#skF_5', '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4972, c_34])).
% 7.18/2.51  tff(c_4997, plain, (k6_domain_1('#skF_5', '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_4981])).
% 7.18/2.51  tff(c_291, plain, (![A_86, B_87]: (r1_tarski(k6_domain_1(A_86, B_87), A_86) | ~m1_subset_1(B_87, A_86) | v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_274, c_22])).
% 7.18/2.51  tff(c_5046, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4997, c_291])).
% 7.18/2.51  tff(c_5069, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), '#skF_5') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4972, c_5046])).
% 7.18/2.51  tff(c_5070, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_5069])).
% 7.18/2.51  tff(c_42, plain, (![B_30, A_28]: (B_30=A_28 | ~r1_tarski(A_28, B_30) | ~v1_zfmisc_1(B_30) | v1_xboole_0(B_30) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.18/2.51  tff(c_5201, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))), inference(resolution, [status(thm)], [c_5070, c_42])).
% 7.18/2.51  tff(c_5222, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_5201])).
% 7.18/2.51  tff(c_5223, plain, (k1_tarski('#skF_1'('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_12, c_58, c_5222])).
% 7.18/2.51  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.18/2.51  tff(c_973, plain, (![A_134, B_135, B_136]: (r2_hidden('#skF_1'(A_134), B_135) | ~r1_tarski(B_136, B_135) | ~r1_tarski(A_134, B_136) | v1_xboole_0(A_134))), inference(resolution, [status(thm)], [c_184, c_6])).
% 7.18/2.51  tff(c_998, plain, (![A_137]: (r2_hidden('#skF_1'(A_137), u1_struct_0('#skF_4')) | ~r1_tarski(A_137, '#skF_5') | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_124, c_973])).
% 7.18/2.51  tff(c_1003, plain, (![A_137]: (m1_subset_1('#skF_1'(A_137), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(A_137, '#skF_5') | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_998, c_14])).
% 7.18/2.51  tff(c_1012, plain, (![A_138]: (m1_subset_1('#skF_1'(A_138), u1_struct_0('#skF_4')) | ~r1_tarski(A_138, '#skF_5') | v1_xboole_0(A_138))), inference(negUnitSimplification, [status(thm)], [c_214, c_1003])).
% 7.18/2.51  tff(c_1015, plain, (![A_138]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_138))=k1_tarski('#skF_1'(A_138)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(A_138, '#skF_5') | v1_xboole_0(A_138))), inference(resolution, [status(thm)], [c_1012, c_34])).
% 7.18/2.51  tff(c_2930, plain, (![A_206]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_206))=k1_tarski('#skF_1'(A_206)) | ~r1_tarski(A_206, '#skF_5') | v1_xboole_0(A_206))), inference(negUnitSimplification, [status(thm)], [c_214, c_1015])).
% 7.18/2.51  tff(c_54, plain, (![A_37, B_39]: (v2_tex_2(k6_domain_1(u1_struct_0(A_37), B_39), A_37) | ~m1_subset_1(B_39, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_173])).
% 7.18/2.51  tff(c_2942, plain, (![A_206]: (v2_tex_2(k1_tarski('#skF_1'(A_206)), '#skF_4') | ~m1_subset_1('#skF_1'(A_206), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_206, '#skF_5') | v1_xboole_0(A_206))), inference(superposition, [status(thm), theory('equality')], [c_2930, c_54])).
% 7.18/2.51  tff(c_2967, plain, (![A_206]: (v2_tex_2(k1_tarski('#skF_1'(A_206)), '#skF_4') | ~m1_subset_1('#skF_1'(A_206), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r1_tarski(A_206, '#skF_5') | v1_xboole_0(A_206))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2942])).
% 7.18/2.51  tff(c_2968, plain, (![A_206]: (v2_tex_2(k1_tarski('#skF_1'(A_206)), '#skF_4') | ~m1_subset_1('#skF_1'(A_206), u1_struct_0('#skF_4')) | ~r1_tarski(A_206, '#skF_5') | v1_xboole_0(A_206))), inference(negUnitSimplification, [status(thm)], [c_66, c_2967])).
% 7.18/2.51  tff(c_5241, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5223, c_2968])).
% 7.18/2.51  tff(c_5276, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_5010, c_5241])).
% 7.18/2.51  tff(c_5278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_80, c_5276])).
% 7.18/2.51  tff(c_5279, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 7.18/2.51  tff(c_6107, plain, (![A_360, B_361]: (~v2_struct_0('#skF_3'(A_360, B_361)) | ~v2_tex_2(B_361, A_360) | ~m1_subset_1(B_361, k1_zfmisc_1(u1_struct_0(A_360))) | v1_xboole_0(B_361) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.18/2.51  tff(c_6137, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_6107])).
% 7.18/2.51  tff(c_6150, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_5279, c_6137])).
% 7.18/2.51  tff(c_6151, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_6150])).
% 7.18/2.51  tff(c_5280, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 7.18/2.51  tff(c_6630, plain, (![A_383, B_384]: (u1_struct_0('#skF_3'(A_383, B_384))=B_384 | ~v2_tex_2(B_384, A_383) | ~m1_subset_1(B_384, k1_zfmisc_1(u1_struct_0(A_383))) | v1_xboole_0(B_384) | ~l1_pre_topc(A_383) | ~v2_pre_topc(A_383) | v2_struct_0(A_383))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.18/2.51  tff(c_6663, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_6630])).
% 7.18/2.51  tff(c_6680, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_5279, c_6663])).
% 7.18/2.51  tff(c_6681, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_6680])).
% 7.18/2.51  tff(c_30, plain, (![A_19]: (v1_zfmisc_1(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | ~v7_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.18/2.51  tff(c_6700, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6681, c_30])).
% 7.18/2.51  tff(c_6709, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_5280, c_6700])).
% 7.18/2.51  tff(c_6711, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_6709])).
% 7.18/2.51  tff(c_62, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.18/2.51  tff(c_6439, plain, (![A_373, B_374]: (v1_tdlat_3('#skF_3'(A_373, B_374)) | ~v2_tex_2(B_374, A_373) | ~m1_subset_1(B_374, k1_zfmisc_1(u1_struct_0(A_373))) | v1_xboole_0(B_374) | ~l1_pre_topc(A_373) | ~v2_pre_topc(A_373) | v2_struct_0(A_373))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.18/2.51  tff(c_6469, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_6439])).
% 7.18/2.51  tff(c_6482, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_5279, c_6469])).
% 7.18/2.51  tff(c_6483, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_6482])).
% 7.18/2.51  tff(c_6785, plain, (![A_392, B_393]: (m1_pre_topc('#skF_3'(A_392, B_393), A_392) | ~v2_tex_2(B_393, A_392) | ~m1_subset_1(B_393, k1_zfmisc_1(u1_struct_0(A_392))) | v1_xboole_0(B_393) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.18/2.51  tff(c_6811, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_6785])).
% 7.18/2.51  tff(c_6829, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_5279, c_6811])).
% 7.18/2.51  tff(c_6830, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_6829])).
% 7.18/2.51  tff(c_38, plain, (![B_27, A_25]: (~v1_tdlat_3(B_27) | v7_struct_0(B_27) | v2_struct_0(B_27) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25) | ~v2_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.18/2.51  tff(c_6833, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_6830, c_38])).
% 7.18/2.51  tff(c_6839, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_6483, c_6833])).
% 7.18/2.51  tff(c_6841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_6151, c_6711, c_6839])).
% 7.18/2.51  tff(c_6842, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_6709])).
% 7.18/2.51  tff(c_6847, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_26, c_6842])).
% 7.18/2.51  tff(c_6897, plain, (![A_399, B_400]: (m1_pre_topc('#skF_3'(A_399, B_400), A_399) | ~v2_tex_2(B_400, A_399) | ~m1_subset_1(B_400, k1_zfmisc_1(u1_struct_0(A_399))) | v1_xboole_0(B_400) | ~l1_pre_topc(A_399) | ~v2_pre_topc(A_399) | v2_struct_0(A_399))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.18/2.51  tff(c_6923, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_6897])).
% 7.18/2.51  tff(c_6941, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_5279, c_6923])).
% 7.18/2.51  tff(c_6942, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_6941])).
% 7.18/2.51  tff(c_28, plain, (![B_18, A_16]: (l1_pre_topc(B_18) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.18/2.51  tff(c_6948, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6942, c_28])).
% 7.18/2.51  tff(c_6955, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6948])).
% 7.18/2.51  tff(c_6957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6847, c_6955])).
% 7.18/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.51  
% 7.18/2.51  Inference rules
% 7.18/2.51  ----------------------
% 7.18/2.51  #Ref     : 0
% 7.18/2.51  #Sup     : 1413
% 7.18/2.51  #Fact    : 0
% 7.18/2.51  #Define  : 0
% 7.18/2.51  #Split   : 25
% 7.18/2.51  #Chain   : 0
% 7.18/2.51  #Close   : 0
% 7.18/2.51  
% 7.18/2.51  Ordering : KBO
% 7.18/2.51  
% 7.18/2.51  Simplification rules
% 7.18/2.51  ----------------------
% 7.18/2.51  #Subsume      : 318
% 7.18/2.51  #Demod        : 297
% 7.18/2.51  #Tautology    : 325
% 7.18/2.51  #SimpNegUnit  : 569
% 7.18/2.51  #BackRed      : 2
% 7.18/2.51  
% 7.18/2.51  #Partial instantiations: 0
% 7.18/2.51  #Strategies tried      : 1
% 7.18/2.51  
% 7.18/2.51  Timing (in seconds)
% 7.18/2.51  ----------------------
% 7.18/2.52  Preprocessing        : 0.33
% 7.18/2.52  Parsing              : 0.17
% 7.18/2.52  CNF conversion       : 0.02
% 7.18/2.52  Main loop            : 1.38
% 7.18/2.52  Inferencing          : 0.46
% 7.18/2.52  Reduction            : 0.41
% 7.18/2.52  Demodulation         : 0.25
% 7.18/2.52  BG Simplification    : 0.05
% 7.18/2.52  Subsumption          : 0.35
% 7.18/2.52  Abstraction          : 0.07
% 7.18/2.52  MUC search           : 0.00
% 7.18/2.52  Cooper               : 0.00
% 7.18/2.52  Total                : 1.78
% 7.18/2.52  Index Insertion      : 0.00
% 7.18/2.52  Index Deletion       : 0.00
% 7.18/2.52  Index Matching       : 0.00
% 7.18/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
