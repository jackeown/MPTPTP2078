%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:02 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 891 expanded)
%              Number of leaves         :   36 ( 298 expanded)
%              Depth                    :   14
%              Number of atoms          :  477 (4582 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k9_tmap_1,type,(
    k9_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_208,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( r1_tsep_1(B,C)
                 => ( v1_funct_1(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),C))
                    & v1_funct_2(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),C),u1_struct_0(C),u1_struct_0(k8_tmap_1(A,B)))
                    & v5_pre_topc(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),C),C,k8_tmap_1(A,B))
                    & m1_subset_1(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),C),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(k8_tmap_1(A,B))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_tmap_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( ~ v2_struct_0(k8_tmap_1(A,B))
        & v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_tmap_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k9_tmap_1(A,B))
        & v1_funct_2(k9_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
        & m1_subset_1(k9_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_tmap_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_178,axiom,(
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
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ( v5_pre_topc(C,B,A)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => r1_tmap_1(B,A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_tsep_1(B,C)
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(C))
                   => r1_tmap_1(C,k8_tmap_1(A,B),k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_tmap_1)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( l1_pre_topc(k8_tmap_1(A_14,B_15))
      | ~ m1_pre_topc(B_15,A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( v2_pre_topc(k8_tmap_1(A_18,B_19))
      | ~ m1_pre_topc(B_19,A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( v1_funct_1(k9_tmap_1(A_16,B_17))
      | ~ m1_pre_topc(B_17,A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( v1_funct_2(k9_tmap_1(A_16,B_17),u1_struct_0(A_16),u1_struct_0(k8_tmap_1(A_16,B_17)))
      | ~ m1_pre_topc(B_17,A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_193,plain,(
    ! [B_122,A_123] :
      ( l1_pre_topc(B_122)
      | ~ m1_pre_topc(B_122,A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_199,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_193])).

tff(c_205,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_199])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k9_tmap_1(A_16,B_17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16),u1_struct_0(k8_tmap_1(A_16,B_17)))))
      | ~ m1_pre_topc(B_17,A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_358,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( v1_funct_2(k2_tmap_1(A_175,B_176,C_177,D_178),u1_struct_0(D_178),u1_struct_0(B_176))
      | ~ l1_struct_0(D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_175),u1_struct_0(B_176))))
      | ~ v1_funct_2(C_177,u1_struct_0(A_175),u1_struct_0(B_176))
      | ~ v1_funct_1(C_177)
      | ~ l1_struct_0(B_176)
      | ~ l1_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_398,plain,(
    ! [A_200,B_201,D_202] :
      ( v1_funct_2(k2_tmap_1(A_200,k8_tmap_1(A_200,B_201),k9_tmap_1(A_200,B_201),D_202),u1_struct_0(D_202),u1_struct_0(k8_tmap_1(A_200,B_201)))
      | ~ l1_struct_0(D_202)
      | ~ v1_funct_2(k9_tmap_1(A_200,B_201),u1_struct_0(A_200),u1_struct_0(k8_tmap_1(A_200,B_201)))
      | ~ v1_funct_1(k9_tmap_1(A_200,B_201))
      | ~ l1_struct_0(k8_tmap_1(A_200,B_201))
      | ~ l1_struct_0(A_200)
      | ~ m1_pre_topc(B_201,A_200)
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(resolution,[status(thm)],[c_24,c_358])).

tff(c_241,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( m1_subset_1(k2_tmap_1(A_150,B_151,C_152,D_153),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_153),u1_struct_0(B_151))))
      | ~ l1_struct_0(D_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_150),u1_struct_0(B_151))))
      | ~ v1_funct_2(C_152,u1_struct_0(A_150),u1_struct_0(B_151))
      | ~ v1_funct_1(C_152)
      | ~ l1_struct_0(B_151)
      | ~ l1_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_63,plain,(
    ! [B_62,A_63] :
      ( l1_pre_topc(B_62)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_75,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_69])).

tff(c_102,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( v1_funct_1(k2_tmap_1(A_82,B_83,C_84,D_85))
      | ~ l1_struct_0(D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_82),u1_struct_0(B_83))))
      | ~ v1_funct_2(C_84,u1_struct_0(A_82),u1_struct_0(B_83))
      | ~ v1_funct_1(C_84)
      | ~ l1_struct_0(B_83)
      | ~ l1_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_131,plain,(
    ! [A_108,B_109,D_110] :
      ( v1_funct_1(k2_tmap_1(A_108,k8_tmap_1(A_108,B_109),k9_tmap_1(A_108,B_109),D_110))
      | ~ l1_struct_0(D_110)
      | ~ v1_funct_2(k9_tmap_1(A_108,B_109),u1_struct_0(A_108),u1_struct_0(k8_tmap_1(A_108,B_109)))
      | ~ v1_funct_1(k9_tmap_1(A_108,B_109))
      | ~ l1_struct_0(k8_tmap_1(A_108,B_109))
      | ~ l1_struct_0(A_108)
      | ~ m1_pre_topc(B_109,A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_24,c_102])).

tff(c_135,plain,(
    ! [A_111,B_112,D_113] :
      ( v1_funct_1(k2_tmap_1(A_111,k8_tmap_1(A_111,B_112),k9_tmap_1(A_111,B_112),D_113))
      | ~ l1_struct_0(D_113)
      | ~ v1_funct_1(k9_tmap_1(A_111,B_112))
      | ~ l1_struct_0(k8_tmap_1(A_111,B_112))
      | ~ l1_struct_0(A_111)
      | ~ m1_pre_topc(B_112,A_111)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_44,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_62,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_138,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_135,c_62])).

tff(c_141,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_138])).

tff(c_142,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_141])).

tff(c_144,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_147,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_144])).

tff(c_151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_147])).

tff(c_152,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_154,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_157,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_154])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_157])).

tff(c_162,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_164,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_168,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_164])).

tff(c_171,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_168])).

tff(c_174,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_171])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_174])).

tff(c_177,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_185,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_177])).

tff(c_188,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_185])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_188])).

tff(c_191,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_227,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_251,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_241,c_227])).

tff(c_252,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_255,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_252])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_255])).

tff(c_260,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_262,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_265,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_262])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_265])).

tff(c_270,plain,
    ( ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_273,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_277,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_273])).

tff(c_280,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_277])).

tff(c_283,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_280])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_283])).

tff(c_286,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_288,plain,(
    ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_291,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_288])).

tff(c_294,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_291])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_294])).

tff(c_297,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_309,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_312,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_309])).

tff(c_315,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_312])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_315])).

tff(c_318,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_335,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_318])).

tff(c_338,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_335])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_338])).

tff(c_341,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_357,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_401,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_398,c_357])).

tff(c_404,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_401])).

tff(c_405,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_404])).

tff(c_406,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_409,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_406])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_409])).

tff(c_414,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_416,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_419,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_416])).

tff(c_423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_419])).

tff(c_424,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_426,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_430,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_426])).

tff(c_433,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_430])).

tff(c_436,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_433])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_436])).

tff(c_439,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_445,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_439])).

tff(c_448,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_445])).

tff(c_451,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_448])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_451])).

tff(c_454,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_458,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_454])).

tff(c_461,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_458])).

tff(c_463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_461])).

tff(c_464,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_212,plain,(
    ! [B_126,A_127] :
      ( v2_pre_topc(B_126)
      | ~ m1_pre_topc(B_126,A_127)
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_218,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_212])).

tff(c_224,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_218])).

tff(c_192,plain,(
    v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_465,plain,(
    v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_342,plain,(
    m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_511,plain,(
    ! [A_221,B_222,C_223] :
      ( m1_subset_1('#skF_1'(A_221,B_222,C_223),u1_struct_0(B_222))
      | v5_pre_topc(C_223,B_222,A_221)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_222),u1_struct_0(A_221))))
      | ~ v1_funct_2(C_223,u1_struct_0(B_222),u1_struct_0(A_221))
      | ~ v1_funct_1(C_223)
      | ~ l1_pre_topc(B_222)
      | ~ v2_pre_topc(B_222)
      | v2_struct_0(B_222)
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_517,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_342,c_511])).

tff(c_522,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_205,c_192,c_465,c_517])).

tff(c_523,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_464,c_522])).

tff(c_529,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_523])).

tff(c_532,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_529])).

tff(c_535,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_532])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_535])).

tff(c_538,plain,
    ( ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_523])).

tff(c_540,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_538])).

tff(c_543,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_540])).

tff(c_546,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_543])).

tff(c_548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_546])).

tff(c_549,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_538])).

tff(c_551,plain,(
    v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_549])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( ~ v2_struct_0(k8_tmap_1(A_18,B_19))
      | ~ m1_pre_topc(B_19,A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_554,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_551,c_34])).

tff(c_557,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_554])).

tff(c_559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_557])).

tff(c_561,plain,(
    ~ v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_549])).

tff(c_46,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_560,plain,(
    m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_549])).

tff(c_539,plain,(
    v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_523])).

tff(c_550,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_538])).

tff(c_36,plain,(
    ! [C_32,A_20,B_28,D_34] :
      ( r1_tmap_1(C_32,k8_tmap_1(A_20,B_28),k2_tmap_1(A_20,k8_tmap_1(A_20,B_28),k9_tmap_1(A_20,B_28),C_32),D_34)
      | ~ m1_subset_1(D_34,u1_struct_0(C_32))
      | ~ r1_tsep_1(B_28,C_32)
      | ~ m1_pre_topc(C_32,A_20)
      | v2_struct_0(C_32)
      | ~ m1_pre_topc(B_28,A_20)
      | v2_struct_0(B_28)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_524,plain,(
    ! [B_224,A_225,C_226] :
      ( ~ r1_tmap_1(B_224,A_225,C_226,'#skF_1'(A_225,B_224,C_226))
      | v5_pre_topc(C_226,B_224,A_225)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_224),u1_struct_0(A_225))))
      | ~ v1_funct_2(C_226,u1_struct_0(B_224),u1_struct_0(A_225))
      | ~ v1_funct_1(C_226)
      | ~ l1_pre_topc(B_224)
      | ~ v2_pre_topc(B_224)
      | v2_struct_0(B_224)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_688,plain,(
    ! [A_291,B_292,C_293] :
      ( v5_pre_topc(k2_tmap_1(A_291,k8_tmap_1(A_291,B_292),k9_tmap_1(A_291,B_292),C_293),C_293,k8_tmap_1(A_291,B_292))
      | ~ m1_subset_1(k2_tmap_1(A_291,k8_tmap_1(A_291,B_292),k9_tmap_1(A_291,B_292),C_293),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_293),u1_struct_0(k8_tmap_1(A_291,B_292)))))
      | ~ v1_funct_2(k2_tmap_1(A_291,k8_tmap_1(A_291,B_292),k9_tmap_1(A_291,B_292),C_293),u1_struct_0(C_293),u1_struct_0(k8_tmap_1(A_291,B_292)))
      | ~ v1_funct_1(k2_tmap_1(A_291,k8_tmap_1(A_291,B_292),k9_tmap_1(A_291,B_292),C_293))
      | ~ l1_pre_topc(C_293)
      | ~ v2_pre_topc(C_293)
      | ~ l1_pre_topc(k8_tmap_1(A_291,B_292))
      | ~ v2_pre_topc(k8_tmap_1(A_291,B_292))
      | v2_struct_0(k8_tmap_1(A_291,B_292))
      | ~ m1_subset_1('#skF_1'(k8_tmap_1(A_291,B_292),C_293,k2_tmap_1(A_291,k8_tmap_1(A_291,B_292),k9_tmap_1(A_291,B_292),C_293)),u1_struct_0(C_293))
      | ~ r1_tsep_1(B_292,C_293)
      | ~ m1_pre_topc(C_293,A_291)
      | v2_struct_0(C_293)
      | ~ m1_pre_topc(B_292,A_291)
      | v2_struct_0(B_292)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(resolution,[status(thm)],[c_36,c_524])).

tff(c_693,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_342,c_688])).

tff(c_697,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_48,c_46,c_560,c_539,c_550,c_224,c_205,c_192,c_465,c_693])).

tff(c_699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_50,c_561,c_464,c_697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.62  
% 3.86/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.62  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.86/1.62  
% 3.86/1.62  %Foreground sorts:
% 3.86/1.62  
% 3.86/1.62  
% 3.86/1.62  %Background operators:
% 3.86/1.62  
% 3.86/1.62  
% 3.86/1.62  %Foreground operators:
% 3.86/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.86/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.86/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.86/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.62  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.86/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.86/1.62  tff(k9_tmap_1, type, k9_tmap_1: ($i * $i) > $i).
% 3.86/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.86/1.62  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 3.86/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.86/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.86/1.62  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.86/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.62  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.86/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.86/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.86/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.62  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.86/1.62  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.86/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.86/1.62  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.86/1.62  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.86/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.86/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.86/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.62  
% 3.86/1.65  tff(f_208, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tsep_1(B, C) => (((v1_funct_1(k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), C)) & v1_funct_2(k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), C), u1_struct_0(C), u1_struct_0(k8_tmap_1(A, B)))) & v5_pre_topc(k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), C), C, k8_tmap_1(A, B))) & m1_subset_1(k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), C), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(k8_tmap_1(A, B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_tmap_1)).
% 3.86/1.65  tff(f_92, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 3.86/1.65  tff(f_123, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((~v2_struct_0(k8_tmap_1(A, B)) & v1_pre_topc(k8_tmap_1(A, B))) & v2_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_tmap_1)).
% 3.86/1.65  tff(f_107, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k9_tmap_1(A, B)) & v1_funct_2(k9_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))) & m1_subset_1(k9_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 3.86/1.65  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.86/1.65  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.86/1.65  tff(f_77, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 3.86/1.65  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.86/1.65  tff(f_178, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tmap_1)).
% 3.86/1.65  tff(f_149, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tsep_1(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k8_tmap_1(A, B), k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_tmap_1)).
% 3.86/1.65  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.86/1.65  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.86/1.65  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.86/1.65  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.86/1.65  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.86/1.65  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.86/1.65  tff(c_18, plain, (![A_14, B_15]: (l1_pre_topc(k8_tmap_1(A_14, B_15)) | ~m1_pre_topc(B_15, A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.86/1.65  tff(c_30, plain, (![A_18, B_19]: (v2_pre_topc(k8_tmap_1(A_18, B_19)) | ~m1_pre_topc(B_19, A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.86/1.65  tff(c_28, plain, (![A_16, B_17]: (v1_funct_1(k9_tmap_1(A_16, B_17)) | ~m1_pre_topc(B_17, A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.86/1.65  tff(c_26, plain, (![A_16, B_17]: (v1_funct_2(k9_tmap_1(A_16, B_17), u1_struct_0(A_16), u1_struct_0(k8_tmap_1(A_16, B_17))) | ~m1_pre_topc(B_17, A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.86/1.65  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.86/1.65  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.86/1.65  tff(c_193, plain, (![B_122, A_123]: (l1_pre_topc(B_122) | ~m1_pre_topc(B_122, A_123) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.86/1.65  tff(c_199, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_193])).
% 3.86/1.65  tff(c_205, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_199])).
% 3.86/1.65  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(k9_tmap_1(A_16, B_17), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16), u1_struct_0(k8_tmap_1(A_16, B_17))))) | ~m1_pre_topc(B_17, A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.86/1.65  tff(c_358, plain, (![A_175, B_176, C_177, D_178]: (v1_funct_2(k2_tmap_1(A_175, B_176, C_177, D_178), u1_struct_0(D_178), u1_struct_0(B_176)) | ~l1_struct_0(D_178) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_175), u1_struct_0(B_176)))) | ~v1_funct_2(C_177, u1_struct_0(A_175), u1_struct_0(B_176)) | ~v1_funct_1(C_177) | ~l1_struct_0(B_176) | ~l1_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.65  tff(c_398, plain, (![A_200, B_201, D_202]: (v1_funct_2(k2_tmap_1(A_200, k8_tmap_1(A_200, B_201), k9_tmap_1(A_200, B_201), D_202), u1_struct_0(D_202), u1_struct_0(k8_tmap_1(A_200, B_201))) | ~l1_struct_0(D_202) | ~v1_funct_2(k9_tmap_1(A_200, B_201), u1_struct_0(A_200), u1_struct_0(k8_tmap_1(A_200, B_201))) | ~v1_funct_1(k9_tmap_1(A_200, B_201)) | ~l1_struct_0(k8_tmap_1(A_200, B_201)) | ~l1_struct_0(A_200) | ~m1_pre_topc(B_201, A_200) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(resolution, [status(thm)], [c_24, c_358])).
% 3.86/1.65  tff(c_241, plain, (![A_150, B_151, C_152, D_153]: (m1_subset_1(k2_tmap_1(A_150, B_151, C_152, D_153), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_153), u1_struct_0(B_151)))) | ~l1_struct_0(D_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_150), u1_struct_0(B_151)))) | ~v1_funct_2(C_152, u1_struct_0(A_150), u1_struct_0(B_151)) | ~v1_funct_1(C_152) | ~l1_struct_0(B_151) | ~l1_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.65  tff(c_63, plain, (![B_62, A_63]: (l1_pre_topc(B_62) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.86/1.65  tff(c_69, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_63])).
% 3.86/1.65  tff(c_75, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_69])).
% 3.86/1.65  tff(c_102, plain, (![A_82, B_83, C_84, D_85]: (v1_funct_1(k2_tmap_1(A_82, B_83, C_84, D_85)) | ~l1_struct_0(D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_82), u1_struct_0(B_83)))) | ~v1_funct_2(C_84, u1_struct_0(A_82), u1_struct_0(B_83)) | ~v1_funct_1(C_84) | ~l1_struct_0(B_83) | ~l1_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.65  tff(c_131, plain, (![A_108, B_109, D_110]: (v1_funct_1(k2_tmap_1(A_108, k8_tmap_1(A_108, B_109), k9_tmap_1(A_108, B_109), D_110)) | ~l1_struct_0(D_110) | ~v1_funct_2(k9_tmap_1(A_108, B_109), u1_struct_0(A_108), u1_struct_0(k8_tmap_1(A_108, B_109))) | ~v1_funct_1(k9_tmap_1(A_108, B_109)) | ~l1_struct_0(k8_tmap_1(A_108, B_109)) | ~l1_struct_0(A_108) | ~m1_pre_topc(B_109, A_108) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(resolution, [status(thm)], [c_24, c_102])).
% 3.86/1.65  tff(c_135, plain, (![A_111, B_112, D_113]: (v1_funct_1(k2_tmap_1(A_111, k8_tmap_1(A_111, B_112), k9_tmap_1(A_111, B_112), D_113)) | ~l1_struct_0(D_113) | ~v1_funct_1(k9_tmap_1(A_111, B_112)) | ~l1_struct_0(k8_tmap_1(A_111, B_112)) | ~l1_struct_0(A_111) | ~m1_pre_topc(B_112, A_111) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_26, c_131])).
% 3.86/1.65  tff(c_44, plain, (~m1_subset_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))))) | ~v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), '#skF_4', k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.86/1.65  tff(c_62, plain, (~v1_funct_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.86/1.65  tff(c_138, plain, (~l1_struct_0('#skF_4') | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_135, c_62])).
% 3.86/1.65  tff(c_141, plain, (~l1_struct_0('#skF_4') | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_138])).
% 3.86/1.65  tff(c_142, plain, (~l1_struct_0('#skF_4') | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_141])).
% 3.86/1.65  tff(c_144, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_142])).
% 3.86/1.65  tff(c_147, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_144])).
% 3.86/1.65  tff(c_151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_147])).
% 3.86/1.65  tff(c_152, plain, (~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_142])).
% 3.86/1.65  tff(c_154, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_152])).
% 3.86/1.65  tff(c_157, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_154])).
% 3.86/1.65  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_157])).
% 3.86/1.65  tff(c_162, plain, (~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_152])).
% 3.86/1.65  tff(c_164, plain, (~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_162])).
% 3.86/1.65  tff(c_168, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_164])).
% 3.86/1.65  tff(c_171, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_168])).
% 3.86/1.65  tff(c_174, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_171])).
% 3.86/1.65  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_174])).
% 3.86/1.65  tff(c_177, plain, (~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_162])).
% 3.86/1.65  tff(c_185, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_177])).
% 3.86/1.65  tff(c_188, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_185])).
% 3.86/1.65  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_188])).
% 3.86/1.65  tff(c_191, plain, (~v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), '#skF_4', k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))))), inference(splitRight, [status(thm)], [c_44])).
% 3.86/1.65  tff(c_227, plain, (~m1_subset_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))))), inference(splitLeft, [status(thm)], [c_191])).
% 3.86/1.65  tff(c_251, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1(k9_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))))) | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_241, c_227])).
% 3.86/1.65  tff(c_252, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_251])).
% 3.86/1.65  tff(c_255, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_252])).
% 3.86/1.65  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_255])).
% 3.86/1.65  tff(c_260, plain, (~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~m1_subset_1(k9_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))))) | ~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_251])).
% 3.86/1.65  tff(c_262, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_260])).
% 3.86/1.65  tff(c_265, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_262])).
% 3.86/1.65  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_265])).
% 3.86/1.65  tff(c_270, plain, (~m1_subset_1(k9_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))))) | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_260])).
% 3.86/1.65  tff(c_273, plain, (~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_270])).
% 3.86/1.65  tff(c_277, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_273])).
% 3.86/1.65  tff(c_280, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_277])).
% 3.86/1.65  tff(c_283, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_280])).
% 3.86/1.65  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_283])).
% 3.86/1.65  tff(c_286, plain, (~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~m1_subset_1(k9_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))))), inference(splitRight, [status(thm)], [c_270])).
% 3.86/1.65  tff(c_288, plain, (~m1_subset_1(k9_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))))), inference(splitLeft, [status(thm)], [c_286])).
% 3.86/1.65  tff(c_291, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_288])).
% 3.86/1.65  tff(c_294, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_291])).
% 3.86/1.65  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_294])).
% 3.86/1.65  tff(c_297, plain, (~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_286])).
% 3.86/1.65  tff(c_309, plain, (~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_297])).
% 3.86/1.65  tff(c_312, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_309])).
% 3.86/1.65  tff(c_315, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_312])).
% 3.86/1.65  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_315])).
% 3.86/1.65  tff(c_318, plain, (~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_297])).
% 3.86/1.65  tff(c_335, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_318])).
% 3.86/1.65  tff(c_338, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_335])).
% 3.86/1.65  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_338])).
% 3.86/1.65  tff(c_341, plain, (~v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), '#skF_4', k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_191])).
% 3.86/1.65  tff(c_357, plain, (~v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_341])).
% 3.86/1.65  tff(c_401, plain, (~l1_struct_0('#skF_4') | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_398, c_357])).
% 3.86/1.65  tff(c_404, plain, (~l1_struct_0('#skF_4') | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_401])).
% 3.86/1.65  tff(c_405, plain, (~l1_struct_0('#skF_4') | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_404])).
% 3.86/1.65  tff(c_406, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_405])).
% 3.86/1.65  tff(c_409, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_406])).
% 3.86/1.65  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_409])).
% 3.86/1.65  tff(c_414, plain, (~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_405])).
% 3.86/1.65  tff(c_416, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_414])).
% 3.86/1.65  tff(c_419, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_416])).
% 3.86/1.65  tff(c_423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_419])).
% 3.86/1.65  tff(c_424, plain, (~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_414])).
% 3.86/1.65  tff(c_426, plain, (~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_424])).
% 3.86/1.65  tff(c_430, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_426])).
% 3.86/1.65  tff(c_433, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_430])).
% 3.86/1.65  tff(c_436, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_433])).
% 3.86/1.65  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_436])).
% 3.86/1.65  tff(c_439, plain, (~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_424])).
% 3.86/1.65  tff(c_445, plain, (~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_439])).
% 3.86/1.65  tff(c_448, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_445])).
% 3.86/1.65  tff(c_451, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_448])).
% 3.86/1.65  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_451])).
% 3.86/1.65  tff(c_454, plain, (~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_439])).
% 3.86/1.65  tff(c_458, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_454])).
% 3.86/1.65  tff(c_461, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_458])).
% 3.86/1.65  tff(c_463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_461])).
% 3.86/1.65  tff(c_464, plain, (~v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), '#skF_4', k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_341])).
% 3.86/1.65  tff(c_212, plain, (![B_126, A_127]: (v2_pre_topc(B_126) | ~m1_pre_topc(B_126, A_127) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.86/1.65  tff(c_218, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_212])).
% 3.86/1.65  tff(c_224, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_218])).
% 3.86/1.65  tff(c_192, plain, (v1_funct_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 3.86/1.65  tff(c_465, plain, (v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_341])).
% 3.86/1.65  tff(c_342, plain, (m1_subset_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))))), inference(splitRight, [status(thm)], [c_191])).
% 3.86/1.65  tff(c_511, plain, (![A_221, B_222, C_223]: (m1_subset_1('#skF_1'(A_221, B_222, C_223), u1_struct_0(B_222)) | v5_pre_topc(C_223, B_222, A_221) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_222), u1_struct_0(A_221)))) | ~v1_funct_2(C_223, u1_struct_0(B_222), u1_struct_0(A_221)) | ~v1_funct_1(C_223) | ~l1_pre_topc(B_222) | ~v2_pre_topc(B_222) | v2_struct_0(B_222) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.86/1.65  tff(c_517, plain, (m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_4', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4')), u1_struct_0('#skF_4')) | v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), '#skF_4', k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_342, c_511])).
% 3.86/1.65  tff(c_522, plain, (m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_4', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4')), u1_struct_0('#skF_4')) | v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), '#skF_4', k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_4') | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_205, c_192, c_465, c_517])).
% 3.86/1.65  tff(c_523, plain, (m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_4', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4')), u1_struct_0('#skF_4')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_464, c_522])).
% 3.86/1.65  tff(c_529, plain, (~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_523])).
% 3.86/1.65  tff(c_532, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_529])).
% 3.86/1.65  tff(c_535, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_532])).
% 3.86/1.65  tff(c_537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_535])).
% 3.86/1.65  tff(c_538, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_4', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_523])).
% 3.86/1.65  tff(c_540, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_538])).
% 3.86/1.65  tff(c_543, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_540])).
% 3.86/1.65  tff(c_546, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_543])).
% 3.86/1.65  tff(c_548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_546])).
% 3.86/1.65  tff(c_549, plain, (m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_4', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4')), u1_struct_0('#skF_4')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_538])).
% 3.86/1.65  tff(c_551, plain, (v2_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_549])).
% 3.86/1.65  tff(c_34, plain, (![A_18, B_19]: (~v2_struct_0(k8_tmap_1(A_18, B_19)) | ~m1_pre_topc(B_19, A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.86/1.65  tff(c_554, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_551, c_34])).
% 3.86/1.65  tff(c_557, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_554])).
% 3.86/1.65  tff(c_559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_557])).
% 3.86/1.65  tff(c_561, plain, (~v2_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_549])).
% 3.86/1.65  tff(c_46, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.86/1.65  tff(c_560, plain, (m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_4', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_549])).
% 3.86/1.65  tff(c_539, plain, (v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_523])).
% 3.86/1.65  tff(c_550, plain, (l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_538])).
% 3.86/1.65  tff(c_36, plain, (![C_32, A_20, B_28, D_34]: (r1_tmap_1(C_32, k8_tmap_1(A_20, B_28), k2_tmap_1(A_20, k8_tmap_1(A_20, B_28), k9_tmap_1(A_20, B_28), C_32), D_34) | ~m1_subset_1(D_34, u1_struct_0(C_32)) | ~r1_tsep_1(B_28, C_32) | ~m1_pre_topc(C_32, A_20) | v2_struct_0(C_32) | ~m1_pre_topc(B_28, A_20) | v2_struct_0(B_28) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.86/1.65  tff(c_524, plain, (![B_224, A_225, C_226]: (~r1_tmap_1(B_224, A_225, C_226, '#skF_1'(A_225, B_224, C_226)) | v5_pre_topc(C_226, B_224, A_225) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_224), u1_struct_0(A_225)))) | ~v1_funct_2(C_226, u1_struct_0(B_224), u1_struct_0(A_225)) | ~v1_funct_1(C_226) | ~l1_pre_topc(B_224) | ~v2_pre_topc(B_224) | v2_struct_0(B_224) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.86/1.65  tff(c_688, plain, (![A_291, B_292, C_293]: (v5_pre_topc(k2_tmap_1(A_291, k8_tmap_1(A_291, B_292), k9_tmap_1(A_291, B_292), C_293), C_293, k8_tmap_1(A_291, B_292)) | ~m1_subset_1(k2_tmap_1(A_291, k8_tmap_1(A_291, B_292), k9_tmap_1(A_291, B_292), C_293), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_293), u1_struct_0(k8_tmap_1(A_291, B_292))))) | ~v1_funct_2(k2_tmap_1(A_291, k8_tmap_1(A_291, B_292), k9_tmap_1(A_291, B_292), C_293), u1_struct_0(C_293), u1_struct_0(k8_tmap_1(A_291, B_292))) | ~v1_funct_1(k2_tmap_1(A_291, k8_tmap_1(A_291, B_292), k9_tmap_1(A_291, B_292), C_293)) | ~l1_pre_topc(C_293) | ~v2_pre_topc(C_293) | ~l1_pre_topc(k8_tmap_1(A_291, B_292)) | ~v2_pre_topc(k8_tmap_1(A_291, B_292)) | v2_struct_0(k8_tmap_1(A_291, B_292)) | ~m1_subset_1('#skF_1'(k8_tmap_1(A_291, B_292), C_293, k2_tmap_1(A_291, k8_tmap_1(A_291, B_292), k9_tmap_1(A_291, B_292), C_293)), u1_struct_0(C_293)) | ~r1_tsep_1(B_292, C_293) | ~m1_pre_topc(C_293, A_291) | v2_struct_0(C_293) | ~m1_pre_topc(B_292, A_291) | v2_struct_0(B_292) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(resolution, [status(thm)], [c_36, c_524])).
% 3.86/1.65  tff(c_693, plain, (v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), '#skF_4', k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_4', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4')), u1_struct_0('#skF_4')) | ~r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_342, c_688])).
% 3.86/1.65  tff(c_697, plain, (v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_4'), '#skF_4', k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_48, c_46, c_560, c_539, c_550, c_224, c_205, c_192, c_465, c_693])).
% 3.86/1.65  tff(c_699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_50, c_561, c_464, c_697])).
% 3.86/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.65  
% 3.86/1.65  Inference rules
% 3.86/1.65  ----------------------
% 3.86/1.65  #Ref     : 0
% 3.86/1.65  #Sup     : 102
% 3.86/1.65  #Fact    : 0
% 3.86/1.65  #Define  : 0
% 3.86/1.65  #Split   : 20
% 3.86/1.65  #Chain   : 0
% 3.86/1.65  #Close   : 0
% 3.86/1.65  
% 3.86/1.65  Ordering : KBO
% 3.86/1.65  
% 3.86/1.65  Simplification rules
% 3.86/1.65  ----------------------
% 3.86/1.65  #Subsume      : 16
% 3.86/1.65  #Demod        : 150
% 3.86/1.65  #Tautology    : 4
% 3.86/1.65  #SimpNegUnit  : 25
% 3.86/1.65  #BackRed      : 0
% 3.86/1.65  
% 3.86/1.65  #Partial instantiations: 0
% 3.86/1.65  #Strategies tried      : 1
% 3.86/1.65  
% 3.86/1.65  Timing (in seconds)
% 3.86/1.65  ----------------------
% 3.86/1.65  Preprocessing        : 0.36
% 3.86/1.65  Parsing              : 0.20
% 3.86/1.65  CNF conversion       : 0.03
% 3.86/1.66  Main loop            : 0.50
% 3.86/1.66  Inferencing          : 0.20
% 3.86/1.66  Reduction            : 0.14
% 3.86/1.66  Demodulation         : 0.09
% 3.86/1.66  BG Simplification    : 0.03
% 3.86/1.66  Subsumption          : 0.10
% 3.86/1.66  Abstraction          : 0.02
% 3.86/1.66  MUC search           : 0.00
% 3.86/1.66  Cooper               : 0.00
% 3.86/1.66  Total                : 0.92
% 3.86/1.66  Index Insertion      : 0.00
% 3.86/1.66  Index Deletion       : 0.00
% 3.86/1.66  Index Matching       : 0.00
% 3.86/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
