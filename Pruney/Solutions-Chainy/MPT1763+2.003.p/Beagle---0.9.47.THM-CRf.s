%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:11 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 465 expanded)
%              Number of leaves         :   42 ( 173 expanded)
%              Depth                    :   15
%              Number of atoms          :  254 (1651 expanded)
%              Number of equality atoms :   26 ( 118 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                   => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_147,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_26,plain,(
    ! [A_25] :
      ( l1_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_62,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_62])).

tff(c_68,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_68])).

tff(c_94,plain,(
    ! [B_92,A_93] :
      ( k1_relat_1(B_92) = A_93
      | ~ v1_partfun1(B_92,A_93)
      | ~ v4_relat_1(B_92,A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_97,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_94])).

tff(c_100,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_97])).

tff(c_101,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_123,plain,(
    ! [C_102,A_103,B_104] :
      ( v1_partfun1(C_102,A_103)
      | ~ v1_funct_2(C_102,A_103,B_104)
      | ~ v1_funct_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | v1_xboole_0(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_126,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_123])).

tff(c_129,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_126])).

tff(c_130,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_129])).

tff(c_28,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(u1_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_133,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_28])).

tff(c_136,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_133])).

tff(c_139,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_136])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_139])).

tff(c_144,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_157,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_40])).

tff(c_156,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_38])).

tff(c_240,plain,(
    ! [A_113,B_114,D_115] :
      ( r2_funct_2(A_113,B_114,D_115,D_115)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_2(D_115,A_113,B_114)
      | ~ v1_funct_1(D_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_242,plain,
    ( r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_156,c_240])).

tff(c_245,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_157,c_242])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_78,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_75])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_4,A_3)),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4])).

tff(c_86,plain,(
    r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_82])).

tff(c_152,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_86])).

tff(c_246,plain,(
    ! [B_116,C_117,A_118] :
      ( m1_pre_topc(B_116,C_117)
      | ~ r1_tarski(u1_struct_0(B_116),u1_struct_0(C_117))
      | ~ m1_pre_topc(C_117,A_118)
      | ~ m1_pre_topc(B_116,A_118)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_263,plain,(
    ! [B_123,A_124] :
      ( m1_pre_topc(B_123,'#skF_3')
      | ~ r1_tarski(u1_struct_0(B_123),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_124)
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_246])).

tff(c_267,plain,(
    ! [A_124] :
      ( m1_pre_topc('#skF_3','#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_124)
      | ~ m1_pre_topc('#skF_3',A_124)
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_263])).

tff(c_270,plain,(
    ! [A_124] :
      ( m1_pre_topc('#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_124)
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_267])).

tff(c_277,plain,(
    ! [A_127] :
      ( ~ m1_pre_topc('#skF_3',A_127)
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_280,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_277])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_280])).

tff(c_285,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_153,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_78])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_146,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k2_partfun1(A_105,B_106,C_107,D_108) = k7_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_148,plain,(
    ! [D_108] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_108) = k7_relat_1('#skF_4',D_108)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_146])).

tff(c_151,plain,(
    ! [D_108] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_108) = k7_relat_1('#skF_4',D_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_148])).

tff(c_229,plain,(
    ! [D_108] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4',D_108) = k7_relat_1('#skF_4',D_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_151])).

tff(c_302,plain,(
    ! [D_137,A_138,C_134,E_136,B_135] :
      ( k3_tmap_1(A_138,B_135,C_134,D_137,E_136) = k2_partfun1(u1_struct_0(C_134),u1_struct_0(B_135),E_136,u1_struct_0(D_137))
      | ~ m1_pre_topc(D_137,C_134)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134),u1_struct_0(B_135))))
      | ~ v1_funct_2(E_136,u1_struct_0(C_134),u1_struct_0(B_135))
      | ~ v1_funct_1(E_136)
      | ~ m1_pre_topc(D_137,A_138)
      | ~ m1_pre_topc(C_134,A_138)
      | ~ l1_pre_topc(B_135)
      | ~ v2_pre_topc(B_135)
      | v2_struct_0(B_135)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_304,plain,(
    ! [A_138,B_135,D_137,E_136] :
      ( k3_tmap_1(A_138,B_135,'#skF_3',D_137,E_136) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_135),E_136,u1_struct_0(D_137))
      | ~ m1_pre_topc(D_137,'#skF_3')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_135))))
      | ~ v1_funct_2(E_136,u1_struct_0('#skF_3'),u1_struct_0(B_135))
      | ~ v1_funct_1(E_136)
      | ~ m1_pre_topc(D_137,A_138)
      | ~ m1_pre_topc('#skF_3',A_138)
      | ~ l1_pre_topc(B_135)
      | ~ v2_pre_topc(B_135)
      | v2_struct_0(B_135)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_302])).

tff(c_310,plain,(
    ! [A_139,B_140,D_141,E_142] :
      ( k3_tmap_1(A_139,B_140,'#skF_3',D_141,E_142) = k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_140),E_142,u1_struct_0(D_141))
      | ~ m1_pre_topc(D_141,'#skF_3')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_140))))
      | ~ v1_funct_2(E_142,k1_relat_1('#skF_4'),u1_struct_0(B_140))
      | ~ v1_funct_1(E_142)
      | ~ m1_pre_topc(D_141,A_139)
      | ~ m1_pre_topc('#skF_3',A_139)
      | ~ l1_pre_topc(B_140)
      | ~ v2_pre_topc(B_140)
      | v2_struct_0(B_140)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_144,c_304])).

tff(c_312,plain,(
    ! [A_139,D_141] :
      ( k3_tmap_1(A_139,'#skF_2','#skF_3',D_141,'#skF_4') = k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_141))
      | ~ m1_pre_topc(D_141,'#skF_3')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_141,A_139)
      | ~ m1_pre_topc('#skF_3',A_139)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_156,c_310])).

tff(c_317,plain,(
    ! [D_141,A_139] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_141)) = k3_tmap_1(A_139,'#skF_2','#skF_3',D_141,'#skF_4')
      | ~ m1_pre_topc(D_141,'#skF_3')
      | ~ m1_pre_topc(D_141,A_139)
      | ~ m1_pre_topc('#skF_3',A_139)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_42,c_157,c_229,c_312])).

tff(c_321,plain,(
    ! [D_143,A_144] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_143)) = k3_tmap_1(A_144,'#skF_2','#skF_3',D_143,'#skF_4')
      | ~ m1_pre_topc(D_143,'#skF_3')
      | ~ m1_pre_topc(D_143,A_144)
      | ~ m1_pre_topc('#skF_3',A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_317])).

tff(c_325,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_321])).

tff(c_332,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_285,c_153,c_144,c_325])).

tff(c_333,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_332])).

tff(c_36,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_154,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_36])).

tff(c_334,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_154])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.39  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.76/1.39  
% 2.76/1.39  %Foreground sorts:
% 2.76/1.39  
% 2.76/1.39  
% 2.76/1.39  %Background operators:
% 2.76/1.39  
% 2.76/1.39  
% 2.76/1.39  %Foreground operators:
% 2.76/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.76/1.39  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.76/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.76/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.76/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.76/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.76/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.39  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.76/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.76/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.76/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.39  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.76/1.39  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.76/1.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.76/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.76/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.76/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.39  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.76/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.39  
% 2.76/1.41  tff(f_178, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.76/1.41  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.76/1.41  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.76/1.41  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.76/1.41  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.76/1.41  tff(f_59, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.76/1.41  tff(f_101, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.76/1.41  tff(f_89, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.76/1.41  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.76/1.41  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.76/1.41  tff(f_147, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.76/1.41  tff(f_73, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.76/1.41  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.76/1.41  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.76/1.41  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.76/1.41  tff(c_26, plain, (![A_25]: (l1_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.41  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.76/1.41  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.76/1.41  tff(c_62, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.76/1.41  tff(c_66, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_62])).
% 2.76/1.41  tff(c_68, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.41  tff(c_72, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_68])).
% 2.76/1.41  tff(c_94, plain, (![B_92, A_93]: (k1_relat_1(B_92)=A_93 | ~v1_partfun1(B_92, A_93) | ~v4_relat_1(B_92, A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.41  tff(c_97, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_94])).
% 2.76/1.41  tff(c_100, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_97])).
% 2.76/1.41  tff(c_101, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_100])).
% 2.76/1.41  tff(c_40, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.76/1.41  tff(c_123, plain, (![C_102, A_103, B_104]: (v1_partfun1(C_102, A_103) | ~v1_funct_2(C_102, A_103, B_104) | ~v1_funct_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | v1_xboole_0(B_104))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.76/1.41  tff(c_126, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_123])).
% 2.76/1.41  tff(c_129, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_126])).
% 2.76/1.41  tff(c_130, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_101, c_129])).
% 2.76/1.41  tff(c_28, plain, (![A_26]: (~v1_xboole_0(u1_struct_0(A_26)) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.76/1.41  tff(c_133, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_130, c_28])).
% 2.76/1.41  tff(c_136, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_133])).
% 2.76/1.41  tff(c_139, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_136])).
% 2.76/1.41  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_139])).
% 2.76/1.41  tff(c_144, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_100])).
% 2.76/1.41  tff(c_157, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_40])).
% 2.76/1.41  tff(c_156, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_38])).
% 2.76/1.41  tff(c_240, plain, (![A_113, B_114, D_115]: (r2_funct_2(A_113, B_114, D_115, D_115) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_2(D_115, A_113, B_114) | ~v1_funct_1(D_115))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.76/1.41  tff(c_242, plain, (r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_156, c_240])).
% 2.76/1.41  tff(c_245, plain, (r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_157, c_242])).
% 2.76/1.41  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.76/1.41  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.76/1.41  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.76/1.41  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.76/1.41  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.41  tff(c_75, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_2])).
% 2.76/1.41  tff(c_78, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_75])).
% 2.76/1.41  tff(c_4, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(k7_relat_1(B_4, A_3)), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.41  tff(c_82, plain, (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_78, c_4])).
% 2.76/1.41  tff(c_86, plain, (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_82])).
% 2.76/1.41  tff(c_152, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_86])).
% 2.76/1.41  tff(c_246, plain, (![B_116, C_117, A_118]: (m1_pre_topc(B_116, C_117) | ~r1_tarski(u1_struct_0(B_116), u1_struct_0(C_117)) | ~m1_pre_topc(C_117, A_118) | ~m1_pre_topc(B_116, A_118) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.76/1.41  tff(c_263, plain, (![B_123, A_124]: (m1_pre_topc(B_123, '#skF_3') | ~r1_tarski(u1_struct_0(B_123), k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_3', A_124) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124))), inference(superposition, [status(thm), theory('equality')], [c_144, c_246])).
% 2.76/1.41  tff(c_267, plain, (![A_124]: (m1_pre_topc('#skF_3', '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_3', A_124) | ~m1_pre_topc('#skF_3', A_124) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124))), inference(superposition, [status(thm), theory('equality')], [c_144, c_263])).
% 2.76/1.41  tff(c_270, plain, (![A_124]: (m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_124) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_267])).
% 2.76/1.41  tff(c_277, plain, (![A_127]: (~m1_pre_topc('#skF_3', A_127) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127))), inference(splitLeft, [status(thm)], [c_270])).
% 2.76/1.41  tff(c_280, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_277])).
% 2.76/1.41  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_280])).
% 2.76/1.41  tff(c_285, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_270])).
% 2.76/1.41  tff(c_153, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_78])).
% 2.76/1.41  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.76/1.41  tff(c_146, plain, (![A_105, B_106, C_107, D_108]: (k2_partfun1(A_105, B_106, C_107, D_108)=k7_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~v1_funct_1(C_107))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.76/1.41  tff(c_148, plain, (![D_108]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_108)=k7_relat_1('#skF_4', D_108) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_146])).
% 2.76/1.41  tff(c_151, plain, (![D_108]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_108)=k7_relat_1('#skF_4', D_108))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_148])).
% 2.76/1.41  tff(c_229, plain, (![D_108]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', D_108)=k7_relat_1('#skF_4', D_108))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_151])).
% 2.76/1.41  tff(c_302, plain, (![D_137, A_138, C_134, E_136, B_135]: (k3_tmap_1(A_138, B_135, C_134, D_137, E_136)=k2_partfun1(u1_struct_0(C_134), u1_struct_0(B_135), E_136, u1_struct_0(D_137)) | ~m1_pre_topc(D_137, C_134) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134), u1_struct_0(B_135)))) | ~v1_funct_2(E_136, u1_struct_0(C_134), u1_struct_0(B_135)) | ~v1_funct_1(E_136) | ~m1_pre_topc(D_137, A_138) | ~m1_pre_topc(C_134, A_138) | ~l1_pre_topc(B_135) | ~v2_pre_topc(B_135) | v2_struct_0(B_135) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.76/1.41  tff(c_304, plain, (![A_138, B_135, D_137, E_136]: (k3_tmap_1(A_138, B_135, '#skF_3', D_137, E_136)=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_135), E_136, u1_struct_0(D_137)) | ~m1_pre_topc(D_137, '#skF_3') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_135)))) | ~v1_funct_2(E_136, u1_struct_0('#skF_3'), u1_struct_0(B_135)) | ~v1_funct_1(E_136) | ~m1_pre_topc(D_137, A_138) | ~m1_pre_topc('#skF_3', A_138) | ~l1_pre_topc(B_135) | ~v2_pre_topc(B_135) | v2_struct_0(B_135) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(superposition, [status(thm), theory('equality')], [c_144, c_302])).
% 2.76/1.41  tff(c_310, plain, (![A_139, B_140, D_141, E_142]: (k3_tmap_1(A_139, B_140, '#skF_3', D_141, E_142)=k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_140), E_142, u1_struct_0(D_141)) | ~m1_pre_topc(D_141, '#skF_3') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_140)))) | ~v1_funct_2(E_142, k1_relat_1('#skF_4'), u1_struct_0(B_140)) | ~v1_funct_1(E_142) | ~m1_pre_topc(D_141, A_139) | ~m1_pre_topc('#skF_3', A_139) | ~l1_pre_topc(B_140) | ~v2_pre_topc(B_140) | v2_struct_0(B_140) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_144, c_304])).
% 2.76/1.41  tff(c_312, plain, (![A_139, D_141]: (k3_tmap_1(A_139, '#skF_2', '#skF_3', D_141, '#skF_4')=k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_141)) | ~m1_pre_topc(D_141, '#skF_3') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_141, A_139) | ~m1_pre_topc('#skF_3', A_139) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(resolution, [status(thm)], [c_156, c_310])).
% 2.76/1.41  tff(c_317, plain, (![D_141, A_139]: (k7_relat_1('#skF_4', u1_struct_0(D_141))=k3_tmap_1(A_139, '#skF_2', '#skF_3', D_141, '#skF_4') | ~m1_pre_topc(D_141, '#skF_3') | ~m1_pre_topc(D_141, A_139) | ~m1_pre_topc('#skF_3', A_139) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_42, c_157, c_229, c_312])).
% 2.76/1.41  tff(c_321, plain, (![D_143, A_144]: (k7_relat_1('#skF_4', u1_struct_0(D_143))=k3_tmap_1(A_144, '#skF_2', '#skF_3', D_143, '#skF_4') | ~m1_pre_topc(D_143, '#skF_3') | ~m1_pre_topc(D_143, A_144) | ~m1_pre_topc('#skF_3', A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(negUnitSimplification, [status(thm)], [c_52, c_317])).
% 2.76/1.41  tff(c_325, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_321])).
% 2.76/1.41  tff(c_332, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_285, c_153, c_144, c_325])).
% 2.76/1.41  tff(c_333, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_332])).
% 2.76/1.41  tff(c_36, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.76/1.41  tff(c_154, plain, (~r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_36])).
% 2.76/1.41  tff(c_334, plain, (~r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_154])).
% 2.76/1.41  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_334])).
% 2.76/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.41  
% 2.76/1.41  Inference rules
% 2.76/1.41  ----------------------
% 2.76/1.41  #Ref     : 0
% 2.76/1.41  #Sup     : 51
% 2.76/1.41  #Fact    : 0
% 2.76/1.41  #Define  : 0
% 2.76/1.41  #Split   : 3
% 2.76/1.41  #Chain   : 0
% 2.76/1.41  #Close   : 0
% 2.76/1.41  
% 2.76/1.41  Ordering : KBO
% 2.76/1.41  
% 2.76/1.41  Simplification rules
% 2.76/1.42  ----------------------
% 2.76/1.42  #Subsume      : 6
% 2.76/1.42  #Demod        : 73
% 2.76/1.42  #Tautology    : 24
% 2.76/1.42  #SimpNegUnit  : 8
% 2.76/1.42  #BackRed      : 7
% 2.76/1.42  
% 2.76/1.42  #Partial instantiations: 0
% 2.76/1.42  #Strategies tried      : 1
% 2.76/1.42  
% 2.76/1.42  Timing (in seconds)
% 2.76/1.42  ----------------------
% 2.76/1.42  Preprocessing        : 0.37
% 2.76/1.42  Parsing              : 0.20
% 2.76/1.42  CNF conversion       : 0.03
% 2.76/1.42  Main loop            : 0.24
% 2.76/1.42  Inferencing          : 0.08
% 2.76/1.42  Reduction            : 0.08
% 2.76/1.42  Demodulation         : 0.06
% 2.76/1.42  BG Simplification    : 0.02
% 2.76/1.42  Subsumption          : 0.04
% 2.76/1.42  Abstraction          : 0.02
% 2.76/1.42  MUC search           : 0.00
% 2.76/1.42  Cooper               : 0.00
% 2.76/1.42  Total                : 0.65
% 2.76/1.42  Index Insertion      : 0.00
% 2.76/1.42  Index Deletion       : 0.00
% 2.76/1.42  Index Matching       : 0.00
% 2.76/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
