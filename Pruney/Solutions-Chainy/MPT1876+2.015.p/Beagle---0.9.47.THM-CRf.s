%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:52 EST 2020

% Result     : Theorem 4.89s
% Output     : CNFRefutation 5.30s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 617 expanded)
%              Number of leaves         :   48 ( 231 expanded)
%              Depth                    :   18
%              Number of atoms          :  357 (2104 expanded)
%              Number of equality atoms :   19 (  76 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_219,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_subset_1)).

tff(f_158,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_199,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_187,axiom,(
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

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_131,axiom,(
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

tff(f_94,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_68,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_72,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_102,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_106,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_102])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_225,plain,(
    ! [C_91,B_92,A_93] :
      ( r2_hidden(C_91,B_92)
      | ~ r2_hidden(C_91,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_231,plain,(
    ! [A_1,B_92] :
      ( r2_hidden('#skF_1'(A_1),B_92)
      | ~ r1_tarski(A_1,B_92)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_225])).

tff(c_14,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_tarski(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,
    ( ~ v1_zfmisc_1('#skF_6')
    | ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_85,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_86,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_82])).

tff(c_108,plain,(
    ! [A_63] :
      ( m1_subset_1('#skF_3'(A_63),k1_zfmisc_1(A_63))
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_112,plain,(
    ! [A_63] :
      ( r1_tarski('#skF_3'(A_63),A_63)
      | v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_108,c_24])).

tff(c_325,plain,(
    ! [B_109,A_110] :
      ( B_109 = A_110
      | ~ r1_tarski(A_110,B_109)
      | ~ v1_zfmisc_1(B_109)
      | v1_xboole_0(B_109)
      | v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_543,plain,(
    ! [A_130] :
      ( '#skF_3'(A_130) = A_130
      | ~ v1_zfmisc_1(A_130)
      | v1_xboole_0('#skF_3'(A_130))
      | v1_xboole_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_112,c_325])).

tff(c_16,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0('#skF_3'(A_14))
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_548,plain,(
    ! [A_131] :
      ( '#skF_3'(A_131) = A_131
      | ~ v1_zfmisc_1(A_131)
      | v1_xboole_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_543,c_16])).

tff(c_554,plain,
    ( '#skF_3'('#skF_6') = '#skF_6'
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_548])).

tff(c_558,plain,(
    '#skF_3'('#skF_6') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_554])).

tff(c_155,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k1_tarski(A_77),k1_zfmisc_1(B_78))
      | ~ r2_hidden(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_164,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k1_tarski(A_77),B_78)
      | ~ r2_hidden(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_155,c_24])).

tff(c_182,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_tarski(A_84,C_85)
      | ~ r1_tarski(B_86,C_85)
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_240,plain,(
    ! [A_96,A_97] :
      ( r1_tarski(A_96,A_97)
      | ~ r1_tarski(A_96,'#skF_3'(A_97))
      | v1_xboole_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_112,c_182])).

tff(c_713,plain,(
    ! [A_142,A_143] :
      ( r1_tarski(k1_tarski(A_142),A_143)
      | v1_xboole_0(A_143)
      | ~ r2_hidden(A_142,'#skF_3'(A_143)) ) ),
    inference(resolution,[status(thm)],[c_164,c_240])).

tff(c_1087,plain,(
    ! [A_173] :
      ( r1_tarski(k1_tarski('#skF_1'('#skF_3'(A_173))),A_173)
      | v1_xboole_0(A_173)
      | v1_xboole_0('#skF_3'(A_173)) ) ),
    inference(resolution,[status(thm)],[c_4,c_713])).

tff(c_1116,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_6')),'#skF_6')
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_3'('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_1087])).

tff(c_1137,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_6')),'#skF_6')
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_1116])).

tff(c_1138,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_66,c_1137])).

tff(c_50,plain,(
    ! [B_41,A_39] :
      ( B_41 = A_39
      | ~ r1_tarski(A_39,B_41)
      | ~ v1_zfmisc_1(B_41)
      | v1_xboole_0(B_41)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1143,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1138,c_50])).

tff(c_1159,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1143])).

tff(c_1160,plain,(
    k1_tarski('#skF_1'('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_66,c_1159])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_tarski(A_16),k1_zfmisc_1(B_17))
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_279,plain,(
    ! [A_100,C_101,B_102] :
      ( m1_subset_1(A_100,C_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(C_101))
      | ~ r2_hidden(A_100,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_391,plain,(
    ! [A_114,B_115,A_116] :
      ( m1_subset_1(A_114,B_115)
      | ~ r2_hidden(A_114,k1_tarski(A_116))
      | ~ r2_hidden(A_116,B_115) ) ),
    inference(resolution,[status(thm)],[c_20,c_279])).

tff(c_400,plain,(
    ! [A_116,B_115] :
      ( m1_subset_1('#skF_1'(k1_tarski(A_116)),B_115)
      | ~ r2_hidden(A_116,B_115)
      | v1_xboole_0(k1_tarski(A_116)) ) ),
    inference(resolution,[status(thm)],[c_4,c_391])).

tff(c_405,plain,(
    ! [A_116,B_115] :
      ( m1_subset_1('#skF_1'(k1_tarski(A_116)),B_115)
      | ~ r2_hidden(A_116,B_115) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_400])).

tff(c_1239,plain,(
    ! [B_175] :
      ( m1_subset_1('#skF_1'('#skF_6'),B_175)
      | ~ r2_hidden('#skF_1'('#skF_6'),B_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1160,c_405])).

tff(c_1243,plain,(
    ! [B_92] :
      ( m1_subset_1('#skF_1'('#skF_6'),B_92)
      | ~ r1_tarski('#skF_6',B_92)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_231,c_1239])).

tff(c_1250,plain,(
    ! [B_92] :
      ( m1_subset_1('#skF_1'('#skF_6'),B_92)
      | ~ r1_tarski('#skF_6',B_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1243])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_165,plain,(
    ! [A_79,B_80] :
      ( ~ r2_hidden('#skF_2'(A_79,B_80),B_80)
      | r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_170,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_126,plain,(
    ! [B_73,A_74] :
      ( v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_135,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_126])).

tff(c_140,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_135])).

tff(c_292,plain,(
    ! [A_103] :
      ( m1_subset_1(A_103,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_103,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_64,c_279])).

tff(c_36,plain,(
    ! [A_31,B_32] :
      ( k6_domain_1(A_31,B_32) = k1_tarski(B_32)
      | ~ m1_subset_1(B_32,A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_295,plain,(
    ! [A_103] :
      ( k6_domain_1(u1_struct_0('#skF_5'),A_103) = k1_tarski(A_103)
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_103,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_292,c_36])).

tff(c_298,plain,(
    ! [A_103] :
      ( k6_domain_1(u1_struct_0('#skF_5'),A_103) = k1_tarski(A_103)
      | ~ r2_hidden(A_103,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_295])).

tff(c_662,plain,(
    ! [A_137,B_138] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_137),B_138),A_137)
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_665,plain,(
    ! [A_103] :
      ( v2_tex_2(k1_tarski(A_103),'#skF_5')
      | ~ m1_subset_1(A_103,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(A_103,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_662])).

tff(c_667,plain,(
    ! [A_103] :
      ( v2_tex_2(k1_tarski(A_103),'#skF_5')
      | ~ m1_subset_1(A_103,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(A_103,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_665])).

tff(c_668,plain,(
    ! [A_103] :
      ( v2_tex_2(k1_tarski(A_103),'#skF_5')
      | ~ m1_subset_1(A_103,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_103,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_667])).

tff(c_1176,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_6'),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_6'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1160,c_668])).

tff(c_1207,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6'),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1176])).

tff(c_1384,plain,(
    ~ r2_hidden('#skF_1'('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1207])).

tff(c_1387,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_231,c_1384])).

tff(c_1393,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_1387])).

tff(c_1395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1393])).

tff(c_1396,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1207])).

tff(c_1446,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1250,c_1396])).

tff(c_1456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1446])).

tff(c_1458,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3392,plain,(
    ! [A_346,B_347] :
      ( m1_pre_topc('#skF_4'(A_346,B_347),A_346)
      | ~ v2_tex_2(B_347,A_346)
      | ~ m1_subset_1(B_347,k1_zfmisc_1(u1_struct_0(A_346)))
      | v1_xboole_0(B_347)
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_3421,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_3392])).

tff(c_3435,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1458,c_3421])).

tff(c_3436,plain,(
    m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_3435])).

tff(c_32,plain,(
    ! [B_29,A_27] :
      ( l1_pre_topc(B_29)
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3442,plain,
    ( l1_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_3436,c_32])).

tff(c_3449,plain,(
    l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3442])).

tff(c_30,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2433,plain,(
    ! [A_300,B_301] :
      ( ~ v2_struct_0('#skF_4'(A_300,B_301))
      | ~ v2_tex_2(B_301,A_300)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_300)))
      | v1_xboole_0(B_301)
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300)
      | v2_struct_0(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_2464,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_2433])).

tff(c_2476,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1458,c_2464])).

tff(c_2477,plain,(
    ~ v2_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_2476])).

tff(c_70,plain,(
    v2_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_48,plain,(
    ! [B_38,A_36] :
      ( v2_tdlat_3(B_38)
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36)
      | ~ v2_tdlat_3(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3439,plain,
    ( v2_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3436,c_48])).

tff(c_3445,plain,
    ( v2_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_3439])).

tff(c_3446,plain,(
    v2_tdlat_3('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3445])).

tff(c_40,plain,(
    ! [A_34] :
      ( v2_pre_topc(A_34)
      | ~ v2_tdlat_3(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3453,plain,
    ( v2_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_3446,c_40])).

tff(c_3543,plain,(
    v2_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3449,c_3453])).

tff(c_3015,plain,(
    ! [A_329,B_330] :
      ( v1_tdlat_3('#skF_4'(A_329,B_330))
      | ~ v2_tex_2(B_330,A_329)
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0(A_329)))
      | v1_xboole_0(B_330)
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | v2_struct_0(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_3050,plain,
    ( v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_3015])).

tff(c_3063,plain,
    ( v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1458,c_3050])).

tff(c_3064,plain,(
    v1_tdlat_3('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_3063])).

tff(c_44,plain,(
    ! [A_35] :
      ( v7_struct_0(A_35)
      | ~ v2_tdlat_3(A_35)
      | ~ v1_tdlat_3(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1457,plain,(
    ~ v1_zfmisc_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3574,plain,(
    ! [A_352,B_353] :
      ( u1_struct_0('#skF_4'(A_352,B_353)) = B_353
      | ~ v2_tex_2(B_353,A_352)
      | ~ m1_subset_1(B_353,k1_zfmisc_1(u1_struct_0(A_352)))
      | v1_xboole_0(B_353)
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_3613,plain,
    ( u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6'
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_3574])).

tff(c_3627,plain,
    ( u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1458,c_3613])).

tff(c_3628,plain,(
    u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_3627])).

tff(c_34,plain,(
    ! [A_30] :
      ( v1_zfmisc_1(u1_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | ~ v7_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3649,plain,
    ( v1_zfmisc_1('#skF_6')
    | ~ l1_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3628,c_34])).

tff(c_3670,plain,
    ( ~ l1_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1457,c_3649])).

tff(c_3672,plain,(
    ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3670])).

tff(c_3675,plain,
    ( ~ v2_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_3672])).

tff(c_3678,plain,(
    v2_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3449,c_3543,c_3064,c_3446,c_3675])).

tff(c_3680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2477,c_3678])).

tff(c_3681,plain,(
    ~ l1_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3670])).

tff(c_3693,plain,(
    ~ l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_3681])).

tff(c_3697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3449,c_3693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.89/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.92  
% 4.89/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.89/1.92  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.89/1.92  
% 4.89/1.92  %Foreground sorts:
% 4.89/1.92  
% 4.89/1.92  
% 4.89/1.92  %Background operators:
% 4.89/1.92  
% 4.89/1.92  
% 4.89/1.92  %Foreground operators:
% 4.89/1.92  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.89/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.89/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.89/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.89/1.92  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.89/1.92  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 4.89/1.92  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.89/1.92  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.89/1.92  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.89/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.89/1.92  tff('#skF_5', type, '#skF_5': $i).
% 4.89/1.92  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.89/1.92  tff('#skF_6', type, '#skF_6': $i).
% 4.89/1.92  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.89/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.89/1.92  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.89/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.89/1.92  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.89/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.89/1.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.89/1.92  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.89/1.92  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.89/1.92  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.89/1.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.89/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.89/1.92  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.89/1.92  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.89/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.89/1.92  
% 5.30/1.95  tff(f_219, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 5.30/1.95  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.30/1.95  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.30/1.95  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.30/1.95  tff(f_47, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 5.30/1.95  tff(f_56, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_subset_1)).
% 5.30/1.95  tff(f_158, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.30/1.95  tff(f_60, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 5.30/1.95  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.30/1.95  tff(f_77, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.30/1.95  tff(f_67, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.30/1.95  tff(f_101, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.30/1.95  tff(f_199, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 5.30/1.95  tff(f_187, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 5.30/1.95  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.30/1.95  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.30/1.95  tff(f_145, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 5.30/1.95  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 5.30/1.95  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_1)).
% 5.30/1.95  tff(f_94, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 5.30/1.95  tff(c_68, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.30/1.95  tff(c_74, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.30/1.95  tff(c_66, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.30/1.95  tff(c_72, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.30/1.95  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.30/1.95  tff(c_102, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~m1_subset_1(A_60, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.30/1.95  tff(c_106, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_102])).
% 5.30/1.95  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.30/1.95  tff(c_225, plain, (![C_91, B_92, A_93]: (r2_hidden(C_91, B_92) | ~r2_hidden(C_91, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.30/1.95  tff(c_231, plain, (![A_1, B_92]: (r2_hidden('#skF_1'(A_1), B_92) | ~r1_tarski(A_1, B_92) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_225])).
% 5.30/1.95  tff(c_14, plain, (![A_13]: (~v1_xboole_0(k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.30/1.95  tff(c_76, plain, (~v1_zfmisc_1('#skF_6') | ~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.30/1.95  tff(c_85, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_76])).
% 5.30/1.95  tff(c_82, plain, (v2_tex_2('#skF_6', '#skF_5') | v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.30/1.95  tff(c_86, plain, (v1_zfmisc_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_85, c_82])).
% 5.30/1.95  tff(c_108, plain, (![A_63]: (m1_subset_1('#skF_3'(A_63), k1_zfmisc_1(A_63)) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.30/1.95  tff(c_24, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.30/1.95  tff(c_112, plain, (![A_63]: (r1_tarski('#skF_3'(A_63), A_63) | v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_108, c_24])).
% 5.30/1.95  tff(c_325, plain, (![B_109, A_110]: (B_109=A_110 | ~r1_tarski(A_110, B_109) | ~v1_zfmisc_1(B_109) | v1_xboole_0(B_109) | v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.30/1.95  tff(c_543, plain, (![A_130]: ('#skF_3'(A_130)=A_130 | ~v1_zfmisc_1(A_130) | v1_xboole_0('#skF_3'(A_130)) | v1_xboole_0(A_130))), inference(resolution, [status(thm)], [c_112, c_325])).
% 5.30/1.95  tff(c_16, plain, (![A_14]: (~v1_xboole_0('#skF_3'(A_14)) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.30/1.95  tff(c_548, plain, (![A_131]: ('#skF_3'(A_131)=A_131 | ~v1_zfmisc_1(A_131) | v1_xboole_0(A_131))), inference(resolution, [status(thm)], [c_543, c_16])).
% 5.30/1.95  tff(c_554, plain, ('#skF_3'('#skF_6')='#skF_6' | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_86, c_548])).
% 5.30/1.95  tff(c_558, plain, ('#skF_3'('#skF_6')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_66, c_554])).
% 5.30/1.95  tff(c_155, plain, (![A_77, B_78]: (m1_subset_1(k1_tarski(A_77), k1_zfmisc_1(B_78)) | ~r2_hidden(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.30/1.95  tff(c_164, plain, (![A_77, B_78]: (r1_tarski(k1_tarski(A_77), B_78) | ~r2_hidden(A_77, B_78))), inference(resolution, [status(thm)], [c_155, c_24])).
% 5.30/1.95  tff(c_182, plain, (![A_84, C_85, B_86]: (r1_tarski(A_84, C_85) | ~r1_tarski(B_86, C_85) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.30/1.95  tff(c_240, plain, (![A_96, A_97]: (r1_tarski(A_96, A_97) | ~r1_tarski(A_96, '#skF_3'(A_97)) | v1_xboole_0(A_97))), inference(resolution, [status(thm)], [c_112, c_182])).
% 5.30/1.95  tff(c_713, plain, (![A_142, A_143]: (r1_tarski(k1_tarski(A_142), A_143) | v1_xboole_0(A_143) | ~r2_hidden(A_142, '#skF_3'(A_143)))), inference(resolution, [status(thm)], [c_164, c_240])).
% 5.30/1.95  tff(c_1087, plain, (![A_173]: (r1_tarski(k1_tarski('#skF_1'('#skF_3'(A_173))), A_173) | v1_xboole_0(A_173) | v1_xboole_0('#skF_3'(A_173)))), inference(resolution, [status(thm)], [c_4, c_713])).
% 5.30/1.95  tff(c_1116, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_6')), '#skF_6') | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_3'('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_558, c_1087])).
% 5.30/1.95  tff(c_1137, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_6')), '#skF_6') | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_558, c_1116])).
% 5.30/1.95  tff(c_1138, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_6')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_1137])).
% 5.30/1.95  tff(c_50, plain, (![B_41, A_39]: (B_41=A_39 | ~r1_tarski(A_39, B_41) | ~v1_zfmisc_1(B_41) | v1_xboole_0(B_41) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.30/1.95  tff(c_1143, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6') | v1_xboole_0(k1_tarski('#skF_1'('#skF_6')))), inference(resolution, [status(thm)], [c_1138, c_50])).
% 5.30/1.95  tff(c_1159, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | v1_xboole_0(k1_tarski('#skF_1'('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1143])).
% 5.30/1.95  tff(c_1160, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_14, c_66, c_1159])).
% 5.30/1.95  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(k1_tarski(A_16), k1_zfmisc_1(B_17)) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.30/1.95  tff(c_279, plain, (![A_100, C_101, B_102]: (m1_subset_1(A_100, C_101) | ~m1_subset_1(B_102, k1_zfmisc_1(C_101)) | ~r2_hidden(A_100, B_102))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.30/1.95  tff(c_391, plain, (![A_114, B_115, A_116]: (m1_subset_1(A_114, B_115) | ~r2_hidden(A_114, k1_tarski(A_116)) | ~r2_hidden(A_116, B_115))), inference(resolution, [status(thm)], [c_20, c_279])).
% 5.30/1.95  tff(c_400, plain, (![A_116, B_115]: (m1_subset_1('#skF_1'(k1_tarski(A_116)), B_115) | ~r2_hidden(A_116, B_115) | v1_xboole_0(k1_tarski(A_116)))), inference(resolution, [status(thm)], [c_4, c_391])).
% 5.30/1.95  tff(c_405, plain, (![A_116, B_115]: (m1_subset_1('#skF_1'(k1_tarski(A_116)), B_115) | ~r2_hidden(A_116, B_115))), inference(negUnitSimplification, [status(thm)], [c_14, c_400])).
% 5.30/1.95  tff(c_1239, plain, (![B_175]: (m1_subset_1('#skF_1'('#skF_6'), B_175) | ~r2_hidden('#skF_1'('#skF_6'), B_175))), inference(superposition, [status(thm), theory('equality')], [c_1160, c_405])).
% 5.30/1.95  tff(c_1243, plain, (![B_92]: (m1_subset_1('#skF_1'('#skF_6'), B_92) | ~r1_tarski('#skF_6', B_92) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_231, c_1239])).
% 5.30/1.95  tff(c_1250, plain, (![B_92]: (m1_subset_1('#skF_1'('#skF_6'), B_92) | ~r1_tarski('#skF_6', B_92))), inference(negUnitSimplification, [status(thm)], [c_66, c_1243])).
% 5.30/1.95  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.30/1.95  tff(c_165, plain, (![A_79, B_80]: (~r2_hidden('#skF_2'(A_79, B_80), B_80) | r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.30/1.95  tff(c_170, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_165])).
% 5.30/1.95  tff(c_126, plain, (![B_73, A_74]: (v1_xboole_0(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.30/1.95  tff(c_135, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_126])).
% 5.30/1.95  tff(c_140, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_135])).
% 5.30/1.95  tff(c_292, plain, (![A_103]: (m1_subset_1(A_103, u1_struct_0('#skF_5')) | ~r2_hidden(A_103, '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_279])).
% 5.30/1.95  tff(c_36, plain, (![A_31, B_32]: (k6_domain_1(A_31, B_32)=k1_tarski(B_32) | ~m1_subset_1(B_32, A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.30/1.95  tff(c_295, plain, (![A_103]: (k6_domain_1(u1_struct_0('#skF_5'), A_103)=k1_tarski(A_103) | v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden(A_103, '#skF_6'))), inference(resolution, [status(thm)], [c_292, c_36])).
% 5.30/1.95  tff(c_298, plain, (![A_103]: (k6_domain_1(u1_struct_0('#skF_5'), A_103)=k1_tarski(A_103) | ~r2_hidden(A_103, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_140, c_295])).
% 5.30/1.95  tff(c_662, plain, (![A_137, B_138]: (v2_tex_2(k6_domain_1(u1_struct_0(A_137), B_138), A_137) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_199])).
% 5.30/1.95  tff(c_665, plain, (![A_103]: (v2_tex_2(k1_tarski(A_103), '#skF_5') | ~m1_subset_1(A_103, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(A_103, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_298, c_662])).
% 5.30/1.95  tff(c_667, plain, (![A_103]: (v2_tex_2(k1_tarski(A_103), '#skF_5') | ~m1_subset_1(A_103, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r2_hidden(A_103, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_665])).
% 5.30/1.95  tff(c_668, plain, (![A_103]: (v2_tex_2(k1_tarski(A_103), '#skF_5') | ~m1_subset_1(A_103, u1_struct_0('#skF_5')) | ~r2_hidden(A_103, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_667])).
% 5.30/1.95  tff(c_1176, plain, (v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_1'('#skF_6'), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'('#skF_6'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1160, c_668])).
% 5.30/1.95  tff(c_1207, plain, (~m1_subset_1('#skF_1'('#skF_6'), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'('#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_85, c_1176])).
% 5.30/1.95  tff(c_1384, plain, (~r2_hidden('#skF_1'('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1207])).
% 5.30/1.95  tff(c_1387, plain, (~r1_tarski('#skF_6', '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_231, c_1384])).
% 5.30/1.95  tff(c_1393, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_1387])).
% 5.30/1.95  tff(c_1395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1393])).
% 5.30/1.95  tff(c_1396, plain, (~m1_subset_1('#skF_1'('#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1207])).
% 5.30/1.95  tff(c_1446, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1250, c_1396])).
% 5.30/1.95  tff(c_1456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_1446])).
% 5.30/1.95  tff(c_1458, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_76])).
% 5.30/1.95  tff(c_3392, plain, (![A_346, B_347]: (m1_pre_topc('#skF_4'(A_346, B_347), A_346) | ~v2_tex_2(B_347, A_346) | ~m1_subset_1(B_347, k1_zfmisc_1(u1_struct_0(A_346))) | v1_xboole_0(B_347) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.30/1.95  tff(c_3421, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_3392])).
% 5.30/1.95  tff(c_3435, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1458, c_3421])).
% 5.30/1.95  tff(c_3436, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_3435])).
% 5.30/1.95  tff(c_32, plain, (![B_29, A_27]: (l1_pre_topc(B_29) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.30/1.95  tff(c_3442, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_3436, c_32])).
% 5.30/1.95  tff(c_3449, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3442])).
% 5.30/1.95  tff(c_30, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.30/1.95  tff(c_2433, plain, (![A_300, B_301]: (~v2_struct_0('#skF_4'(A_300, B_301)) | ~v2_tex_2(B_301, A_300) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_300))) | v1_xboole_0(B_301) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300) | v2_struct_0(A_300))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.30/1.95  tff(c_2464, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_2433])).
% 5.30/1.95  tff(c_2476, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1458, c_2464])).
% 5.30/1.95  tff(c_2477, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_2476])).
% 5.30/1.95  tff(c_70, plain, (v2_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 5.30/1.95  tff(c_48, plain, (![B_38, A_36]: (v2_tdlat_3(B_38) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36) | ~v2_tdlat_3(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.30/1.95  tff(c_3439, plain, (v2_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_3436, c_48])).
% 5.30/1.95  tff(c_3445, plain, (v2_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_3439])).
% 5.30/1.95  tff(c_3446, plain, (v2_tdlat_3('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_3445])).
% 5.30/1.95  tff(c_40, plain, (![A_34]: (v2_pre_topc(A_34) | ~v2_tdlat_3(A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.30/1.95  tff(c_3453, plain, (v2_pre_topc('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_3446, c_40])).
% 5.30/1.95  tff(c_3543, plain, (v2_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3449, c_3453])).
% 5.30/1.95  tff(c_3015, plain, (![A_329, B_330]: (v1_tdlat_3('#skF_4'(A_329, B_330)) | ~v2_tex_2(B_330, A_329) | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0(A_329))) | v1_xboole_0(B_330) | ~l1_pre_topc(A_329) | ~v2_pre_topc(A_329) | v2_struct_0(A_329))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.30/1.95  tff(c_3050, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_3015])).
% 5.30/1.95  tff(c_3063, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1458, c_3050])).
% 5.30/1.95  tff(c_3064, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_3063])).
% 5.30/1.95  tff(c_44, plain, (![A_35]: (v7_struct_0(A_35) | ~v2_tdlat_3(A_35) | ~v1_tdlat_3(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.30/1.95  tff(c_1457, plain, (~v1_zfmisc_1('#skF_6')), inference(splitRight, [status(thm)], [c_76])).
% 5.30/1.95  tff(c_3574, plain, (![A_352, B_353]: (u1_struct_0('#skF_4'(A_352, B_353))=B_353 | ~v2_tex_2(B_353, A_352) | ~m1_subset_1(B_353, k1_zfmisc_1(u1_struct_0(A_352))) | v1_xboole_0(B_353) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.30/1.95  tff(c_3613, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6' | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_3574])).
% 5.30/1.95  tff(c_3627, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1458, c_3613])).
% 5.30/1.95  tff(c_3628, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_3627])).
% 5.30/1.95  tff(c_34, plain, (![A_30]: (v1_zfmisc_1(u1_struct_0(A_30)) | ~l1_struct_0(A_30) | ~v7_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.30/1.95  tff(c_3649, plain, (v1_zfmisc_1('#skF_6') | ~l1_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3628, c_34])).
% 5.30/1.95  tff(c_3670, plain, (~l1_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1457, c_3649])).
% 5.30/1.95  tff(c_3672, plain, (~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_3670])).
% 5.30/1.95  tff(c_3675, plain, (~v2_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~v2_pre_topc('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_3672])).
% 5.30/1.95  tff(c_3678, plain, (v2_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3449, c_3543, c_3064, c_3446, c_3675])).
% 5.30/1.95  tff(c_3680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2477, c_3678])).
% 5.30/1.95  tff(c_3681, plain, (~l1_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_3670])).
% 5.30/1.95  tff(c_3693, plain, (~l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_3681])).
% 5.30/1.95  tff(c_3697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3449, c_3693])).
% 5.30/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.30/1.95  
% 5.30/1.95  Inference rules
% 5.30/1.95  ----------------------
% 5.30/1.95  #Ref     : 0
% 5.30/1.95  #Sup     : 813
% 5.30/1.95  #Fact    : 0
% 5.30/1.95  #Define  : 0
% 5.30/1.95  #Split   : 11
% 5.30/1.95  #Chain   : 0
% 5.30/1.95  #Close   : 0
% 5.30/1.95  
% 5.30/1.95  Ordering : KBO
% 5.30/1.95  
% 5.30/1.95  Simplification rules
% 5.30/1.95  ----------------------
% 5.30/1.95  #Subsume      : 121
% 5.30/1.95  #Demod        : 109
% 5.30/1.95  #Tautology    : 115
% 5.30/1.95  #SimpNegUnit  : 148
% 5.30/1.95  #BackRed      : 2
% 5.30/1.95  
% 5.30/1.95  #Partial instantiations: 0
% 5.30/1.95  #Strategies tried      : 1
% 5.30/1.95  
% 5.30/1.95  Timing (in seconds)
% 5.30/1.95  ----------------------
% 5.30/1.95  Preprocessing        : 0.34
% 5.30/1.95  Parsing              : 0.18
% 5.30/1.95  CNF conversion       : 0.02
% 5.30/1.95  Main loop            : 0.82
% 5.30/1.95  Inferencing          : 0.28
% 5.30/1.95  Reduction            : 0.24
% 5.30/1.95  Demodulation         : 0.15
% 5.30/1.95  BG Simplification    : 0.04
% 5.30/1.95  Subsumption          : 0.19
% 5.30/1.95  Abstraction          : 0.04
% 5.30/1.95  MUC search           : 0.00
% 5.30/1.95  Cooper               : 0.00
% 5.30/1.95  Total                : 1.21
% 5.30/1.95  Index Insertion      : 0.00
% 5.30/1.95  Index Deletion       : 0.00
% 5.30/1.95  Index Matching       : 0.00
% 5.30/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
