%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:14 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 146 expanded)
%              Number of leaves         :   30 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  206 ( 949 expanded)
%              Number of equality atoms :   23 (  64 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
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
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(B)))
                             => ( r1_tarski(k8_relset_1(u1_struct_0(D),u1_struct_0(B),E,F),u1_struct_0(C))
                               => k8_relset_1(u1_struct_0(D),u1_struct_0(B),E,F) = k8_relset_1(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_135,axiom,(
    ! [A] :
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
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ( r1_tarski(k8_relset_1(u1_struct_0(A),u1_struct_0(B),D,E),u1_struct_0(C))
                       => k8_relset_1(u1_struct_0(A),u1_struct_0(B),D,E) = k8_relset_1(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tmap_1)).

tff(f_100,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_26,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_64,plain,(
    ! [B_143,A_144] :
      ( v2_pre_topc(B_143)
      | ~ m1_pre_topc(B_143,A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_82,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_73])).

tff(c_45,plain,(
    ! [B_141,A_142] :
      ( l1_pre_topc(B_141)
      | ~ m1_pre_topc(B_141,A_142)
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_54,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_61,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_54])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_18,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_24,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_22,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_16,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_14,plain,(
    r1_tarski(k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_166,plain,(
    ! [C_160,B_159,D_158,A_157,E_161] :
      ( k8_relset_1(u1_struct_0(C_160),u1_struct_0(B_159),k2_tmap_1(A_157,B_159,D_158,C_160),E_161) = k8_relset_1(u1_struct_0(A_157),u1_struct_0(B_159),D_158,E_161)
      | ~ r1_tarski(k8_relset_1(u1_struct_0(A_157),u1_struct_0(B_159),D_158,E_161),u1_struct_0(C_160))
      | ~ m1_subset_1(E_161,k1_zfmisc_1(u1_struct_0(B_159)))
      | ~ m1_subset_1(D_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_157),u1_struct_0(B_159))))
      | ~ v1_funct_2(D_158,u1_struct_0(A_157),u1_struct_0(B_159))
      | ~ v1_funct_1(D_158)
      | ~ m1_pre_topc(C_160,A_157)
      | v2_struct_0(C_160)
      | ~ l1_pre_topc(B_159)
      | ~ v2_pre_topc(B_159)
      | v2_struct_0(B_159)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_168,plain,
    ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') = k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_166])).

tff(c_171,plain,
    ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') = k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_61,c_36,c_34,c_18,c_24,c_22,c_20,c_16,c_168])).

tff(c_172,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') = k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_38,c_32,c_171])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_101,plain,(
    ! [C_154,D_150,B_152,E_153,A_151] :
      ( k3_tmap_1(A_151,B_152,C_154,D_150,E_153) = k2_partfun1(u1_struct_0(C_154),u1_struct_0(B_152),E_153,u1_struct_0(D_150))
      | ~ m1_pre_topc(D_150,C_154)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_154),u1_struct_0(B_152))))
      | ~ v1_funct_2(E_153,u1_struct_0(C_154),u1_struct_0(B_152))
      | ~ v1_funct_1(E_153)
      | ~ m1_pre_topc(D_150,A_151)
      | ~ m1_pre_topc(C_154,A_151)
      | ~ l1_pre_topc(B_152)
      | ~ v2_pre_topc(B_152)
      | v2_struct_0(B_152)
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_103,plain,(
    ! [A_151,D_150] :
      ( k3_tmap_1(A_151,'#skF_2','#skF_4',D_150,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_150))
      | ~ m1_pre_topc(D_150,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_150,A_151)
      | ~ m1_pre_topc('#skF_4',A_151)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_20,c_101])).

tff(c_106,plain,(
    ! [A_151,D_150] :
      ( k3_tmap_1(A_151,'#skF_2','#skF_4',D_150,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_150))
      | ~ m1_pre_topc(D_150,'#skF_4')
      | ~ m1_pre_topc(D_150,A_151)
      | ~ m1_pre_topc('#skF_4',A_151)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_24,c_22,c_103])).

tff(c_108,plain,(
    ! [A_155,D_156] :
      ( k3_tmap_1(A_155,'#skF_2','#skF_4',D_156,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_156))
      | ~ m1_pre_topc(D_156,'#skF_4')
      | ~ m1_pre_topc(D_156,A_155)
      | ~ m1_pre_topc('#skF_4',A_155)
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_106])).

tff(c_110,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_108])).

tff(c_117,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_26,c_18,c_110])).

tff(c_118,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_117])).

tff(c_85,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( k2_partfun1(u1_struct_0(A_145),u1_struct_0(B_146),C_147,u1_struct_0(D_148)) = k2_tmap_1(A_145,B_146,C_147,D_148)
      | ~ m1_pre_topc(D_148,A_145)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_145),u1_struct_0(B_146))))
      | ~ v1_funct_2(C_147,u1_struct_0(A_145),u1_struct_0(B_146))
      | ~ v1_funct_1(C_147)
      | ~ l1_pre_topc(B_146)
      | ~ v2_pre_topc(B_146)
      | v2_struct_0(B_146)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_87,plain,(
    ! [D_148] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_148)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_148)
      | ~ m1_pre_topc(D_148,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_85])).

tff(c_90,plain,(
    ! [D_148] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_148)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_148)
      | ~ m1_pre_topc(D_148,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_61,c_36,c_34,c_24,c_22,c_87])).

tff(c_91,plain,(
    ! [D_148] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_148)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_148)
      | ~ m1_pre_topc(D_148,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_38,c_90])).

tff(c_130,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_91])).

tff(c_137,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_130])).

tff(c_12,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_142,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') != k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_12])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:35:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.38  
% 2.28/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.39  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k8_relset_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.28/1.39  
% 2.28/1.39  %Foreground sorts:
% 2.28/1.39  
% 2.28/1.39  
% 2.28/1.39  %Background operators:
% 2.28/1.39  
% 2.28/1.39  
% 2.28/1.39  %Foreground operators:
% 2.28/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.28/1.39  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.39  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.28/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.28/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.28/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.28/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.39  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.28/1.39  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.28/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.28/1.39  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.28/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.28/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.39  
% 2.63/1.40  tff(f_179, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(D), u1_struct_0(B), E, F), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tmap_1)).
% 2.63/1.40  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.63/1.40  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.63/1.40  tff(f_135, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E), u1_struct_0(C)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), D, E) = k8_relset_1(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tmap_1)).
% 2.63/1.40  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.63/1.40  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.63/1.40  tff(c_28, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_32, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_26, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_64, plain, (![B_143, A_144]: (v2_pre_topc(B_143) | ~m1_pre_topc(B_143, A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.63/1.40  tff(c_73, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_64])).
% 2.63/1.40  tff(c_82, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_73])).
% 2.63/1.40  tff(c_45, plain, (![B_141, A_142]: (l1_pre_topc(B_141) | ~m1_pre_topc(B_141, A_142) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.63/1.40  tff(c_54, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_45])).
% 2.63/1.40  tff(c_61, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_54])).
% 2.63/1.40  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_18, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_24, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_22, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_20, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_16, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_14, plain, (r1_tarski(k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_166, plain, (![C_160, B_159, D_158, A_157, E_161]: (k8_relset_1(u1_struct_0(C_160), u1_struct_0(B_159), k2_tmap_1(A_157, B_159, D_158, C_160), E_161)=k8_relset_1(u1_struct_0(A_157), u1_struct_0(B_159), D_158, E_161) | ~r1_tarski(k8_relset_1(u1_struct_0(A_157), u1_struct_0(B_159), D_158, E_161), u1_struct_0(C_160)) | ~m1_subset_1(E_161, k1_zfmisc_1(u1_struct_0(B_159))) | ~m1_subset_1(D_158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_157), u1_struct_0(B_159)))) | ~v1_funct_2(D_158, u1_struct_0(A_157), u1_struct_0(B_159)) | ~v1_funct_1(D_158) | ~m1_pre_topc(C_160, A_157) | v2_struct_0(C_160) | ~l1_pre_topc(B_159) | ~v2_pre_topc(B_159) | v2_struct_0(B_159) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.63/1.40  tff(c_168, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')=k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_14, c_166])).
% 2.63/1.40  tff(c_171, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')=k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_61, c_36, c_34, c_18, c_24, c_22, c_20, c_16, c_168])).
% 2.63/1.40  tff(c_172, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')=k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_28, c_38, c_32, c_171])).
% 2.63/1.40  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_101, plain, (![C_154, D_150, B_152, E_153, A_151]: (k3_tmap_1(A_151, B_152, C_154, D_150, E_153)=k2_partfun1(u1_struct_0(C_154), u1_struct_0(B_152), E_153, u1_struct_0(D_150)) | ~m1_pre_topc(D_150, C_154) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_154), u1_struct_0(B_152)))) | ~v1_funct_2(E_153, u1_struct_0(C_154), u1_struct_0(B_152)) | ~v1_funct_1(E_153) | ~m1_pre_topc(D_150, A_151) | ~m1_pre_topc(C_154, A_151) | ~l1_pre_topc(B_152) | ~v2_pre_topc(B_152) | v2_struct_0(B_152) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.63/1.40  tff(c_103, plain, (![A_151, D_150]: (k3_tmap_1(A_151, '#skF_2', '#skF_4', D_150, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_150)) | ~m1_pre_topc(D_150, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_150, A_151) | ~m1_pre_topc('#skF_4', A_151) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(resolution, [status(thm)], [c_20, c_101])).
% 2.63/1.40  tff(c_106, plain, (![A_151, D_150]: (k3_tmap_1(A_151, '#skF_2', '#skF_4', D_150, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_150)) | ~m1_pre_topc(D_150, '#skF_4') | ~m1_pre_topc(D_150, A_151) | ~m1_pre_topc('#skF_4', A_151) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_24, c_22, c_103])).
% 2.63/1.40  tff(c_108, plain, (![A_155, D_156]: (k3_tmap_1(A_155, '#skF_2', '#skF_4', D_156, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_156)) | ~m1_pre_topc(D_156, '#skF_4') | ~m1_pre_topc(D_156, A_155) | ~m1_pre_topc('#skF_4', A_155) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(negUnitSimplification, [status(thm)], [c_38, c_106])).
% 2.63/1.40  tff(c_110, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_108])).
% 2.63/1.40  tff(c_117, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_26, c_18, c_110])).
% 2.63/1.40  tff(c_118, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_117])).
% 2.63/1.40  tff(c_85, plain, (![A_145, B_146, C_147, D_148]: (k2_partfun1(u1_struct_0(A_145), u1_struct_0(B_146), C_147, u1_struct_0(D_148))=k2_tmap_1(A_145, B_146, C_147, D_148) | ~m1_pre_topc(D_148, A_145) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_145), u1_struct_0(B_146)))) | ~v1_funct_2(C_147, u1_struct_0(A_145), u1_struct_0(B_146)) | ~v1_funct_1(C_147) | ~l1_pre_topc(B_146) | ~v2_pre_topc(B_146) | v2_struct_0(B_146) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.63/1.40  tff(c_87, plain, (![D_148]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_148))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_148) | ~m1_pre_topc(D_148, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_85])).
% 2.63/1.40  tff(c_90, plain, (![D_148]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_148))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_148) | ~m1_pre_topc(D_148, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_61, c_36, c_34, c_24, c_22, c_87])).
% 2.63/1.40  tff(c_91, plain, (![D_148]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_148))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_148) | ~m1_pre_topc(D_148, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_28, c_38, c_90])).
% 2.63/1.40  tff(c_130, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_118, c_91])).
% 2.63/1.40  tff(c_137, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_130])).
% 2.63/1.40  tff(c_12, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.63/1.40  tff(c_142, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')!=k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_12])).
% 2.63/1.40  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_142])).
% 2.63/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.40  
% 2.63/1.40  Inference rules
% 2.63/1.40  ----------------------
% 2.63/1.40  #Ref     : 0
% 2.63/1.40  #Sup     : 27
% 2.63/1.40  #Fact    : 0
% 2.63/1.40  #Define  : 0
% 2.63/1.40  #Split   : 1
% 2.63/1.40  #Chain   : 0
% 2.63/1.40  #Close   : 0
% 2.63/1.40  
% 2.63/1.40  Ordering : KBO
% 2.63/1.40  
% 2.63/1.40  Simplification rules
% 2.63/1.40  ----------------------
% 2.63/1.40  #Subsume      : 1
% 2.63/1.40  #Demod        : 55
% 2.63/1.40  #Tautology    : 15
% 2.63/1.40  #SimpNegUnit  : 7
% 2.63/1.40  #BackRed      : 2
% 2.63/1.40  
% 2.63/1.40  #Partial instantiations: 0
% 2.63/1.40  #Strategies tried      : 1
% 2.63/1.40  
% 2.63/1.40  Timing (in seconds)
% 2.63/1.40  ----------------------
% 2.63/1.41  Preprocessing        : 0.40
% 2.63/1.41  Parsing              : 0.22
% 2.63/1.41  CNF conversion       : 0.05
% 2.63/1.41  Main loop            : 0.22
% 2.63/1.41  Inferencing          : 0.08
% 2.63/1.41  Reduction            : 0.08
% 2.63/1.41  Demodulation         : 0.06
% 2.63/1.41  BG Simplification    : 0.02
% 2.63/1.41  Subsumption          : 0.04
% 2.63/1.41  Abstraction          : 0.01
% 2.63/1.41  MUC search           : 0.00
% 2.63/1.41  Cooper               : 0.00
% 2.63/1.41  Total                : 0.66
% 2.63/1.41  Index Insertion      : 0.00
% 2.63/1.41  Index Deletion       : 0.00
% 2.63/1.41  Index Matching       : 0.00
% 2.63/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
