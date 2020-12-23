%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:02 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 883 expanded)
%              Number of leaves         :   34 ( 293 expanded)
%              Depth                    :   14
%              Number of atoms          :  452 (3954 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_192,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( v1_funct_1(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B))
              & v1_funct_2(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),u1_struct_0(B),u1_struct_0(k8_tmap_1(A,B)))
              & v5_pre_topc(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),B,k8_tmap_1(A,B))
              & m1_subset_1(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(k8_tmap_1(A,B))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_tmap_1)).

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

tff(f_170,axiom,(
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

tff(f_141,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => r1_tmap_1(B,k8_tmap_1(A,B),k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_tmap_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

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

tff(c_56,plain,(
    ! [B_51,A_52] :
      ( l1_pre_topc(B_51)
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_59,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_56])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_59])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k9_tmap_1(A_16,B_17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16),u1_struct_0(k8_tmap_1(A_16,B_17)))))
      | ~ m1_pre_topc(B_17,A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_321,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( v1_funct_2(k2_tmap_1(A_158,B_159,C_160,D_161),u1_struct_0(D_161),u1_struct_0(B_159))
      | ~ l1_struct_0(D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158),u1_struct_0(B_159))))
      | ~ v1_funct_2(C_160,u1_struct_0(A_158),u1_struct_0(B_159))
      | ~ v1_funct_1(C_160)
      | ~ l1_struct_0(B_159)
      | ~ l1_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_361,plain,(
    ! [A_182,B_183,D_184] :
      ( v1_funct_2(k2_tmap_1(A_182,k8_tmap_1(A_182,B_183),k9_tmap_1(A_182,B_183),D_184),u1_struct_0(D_184),u1_struct_0(k8_tmap_1(A_182,B_183)))
      | ~ l1_struct_0(D_184)
      | ~ v1_funct_2(k9_tmap_1(A_182,B_183),u1_struct_0(A_182),u1_struct_0(k8_tmap_1(A_182,B_183)))
      | ~ v1_funct_1(k9_tmap_1(A_182,B_183))
      | ~ l1_struct_0(k8_tmap_1(A_182,B_183))
      | ~ l1_struct_0(A_182)
      | ~ m1_pre_topc(B_183,A_182)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_24,c_321])).

tff(c_200,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( m1_subset_1(k2_tmap_1(A_133,B_134,C_135,D_136),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_136),u1_struct_0(B_134))))
      | ~ l1_struct_0(D_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_133),u1_struct_0(B_134))))
      | ~ v1_funct_2(C_135,u1_struct_0(A_133),u1_struct_0(B_134))
      | ~ v1_funct_1(C_135)
      | ~ l1_struct_0(B_134)
      | ~ l1_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_84,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( v1_funct_1(k2_tmap_1(A_71,B_72,C_73,D_74))
      | ~ l1_struct_0(D_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0(B_72))))
      | ~ v1_funct_2(C_73,u1_struct_0(A_71),u1_struct_0(B_72))
      | ~ v1_funct_1(C_73)
      | ~ l1_struct_0(B_72)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_113,plain,(
    ! [A_96,B_97,D_98] :
      ( v1_funct_1(k2_tmap_1(A_96,k8_tmap_1(A_96,B_97),k9_tmap_1(A_96,B_97),D_98))
      | ~ l1_struct_0(D_98)
      | ~ v1_funct_2(k9_tmap_1(A_96,B_97),u1_struct_0(A_96),u1_struct_0(k8_tmap_1(A_96,B_97)))
      | ~ v1_funct_1(k9_tmap_1(A_96,B_97))
      | ~ l1_struct_0(k8_tmap_1(A_96,B_97))
      | ~ l1_struct_0(A_96)
      | ~ m1_pre_topc(B_97,A_96)
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_24,c_84])).

tff(c_117,plain,(
    ! [A_99,B_100,D_101] :
      ( v1_funct_1(k2_tmap_1(A_99,k8_tmap_1(A_99,B_100),k9_tmap_1(A_99,B_100),D_101))
      | ~ l1_struct_0(D_101)
      | ~ v1_funct_1(k9_tmap_1(A_99,B_100))
      | ~ l1_struct_0(k8_tmap_1(A_99,B_100))
      | ~ l1_struct_0(A_99)
      | ~ m1_pre_topc(B_100,A_99)
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_26,c_113])).

tff(c_44,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_64,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_120,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_117,c_64])).

tff(c_123,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_120])).

tff(c_124,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_123])).

tff(c_125,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_128,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_125])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_128])).

tff(c_133,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_135,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_138,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_135])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_138])).

tff(c_143,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_146,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_150,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_146])).

tff(c_153,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_150])).

tff(c_156,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_153])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_156])).

tff(c_159,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_163,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_159])).

tff(c_166,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_163])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_166])).

tff(c_169,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_186,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_210,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_200,c_186])).

tff(c_211,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_214,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_211])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_214])).

tff(c_219,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_221,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_224,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_221])).

tff(c_228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_224])).

tff(c_229,plain,
    ( ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_238,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_242,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_238])).

tff(c_245,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_242])).

tff(c_248,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_245])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_248])).

tff(c_251,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_253,plain,(
    ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_256,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_253])).

tff(c_259,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_256])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_259])).

tff(c_262,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_280,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_283,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_280])).

tff(c_286,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_283])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_286])).

tff(c_289,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_298,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_289])).

tff(c_301,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_298])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_301])).

tff(c_304,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_320,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_364,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_361,c_320])).

tff(c_367,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_364])).

tff(c_368,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_367])).

tff(c_369,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_372,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_369])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_372])).

tff(c_377,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_379,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_377])).

tff(c_382,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_379])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_382])).

tff(c_387,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_389,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_393,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_389])).

tff(c_396,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_393])).

tff(c_399,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_396])).

tff(c_401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_399])).

tff(c_402,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_408,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_402])).

tff(c_411,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_408])).

tff(c_414,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_411])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_414])).

tff(c_417,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_421,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_417])).

tff(c_424,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_421])).

tff(c_426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_424])).

tff(c_427,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_176,plain,(
    ! [B_106,A_107] :
      ( v2_pre_topc(B_106)
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_179,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_176])).

tff(c_182,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_179])).

tff(c_170,plain,(
    v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_428,plain,(
    v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_305,plain,(
    m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_473,plain,(
    ! [A_199,B_200,C_201] :
      ( m1_subset_1('#skF_1'(A_199,B_200,C_201),u1_struct_0(B_200))
      | v5_pre_topc(C_201,B_200,A_199)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_200),u1_struct_0(A_199))))
      | ~ v1_funct_2(C_201,u1_struct_0(B_200),u1_struct_0(A_199))
      | ~ v1_funct_1(C_201)
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_479,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_305,c_473])).

tff(c_484,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_62,c_170,c_428,c_479])).

tff(c_485,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_427,c_484])).

tff(c_486,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_494,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_486])).

tff(c_497,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_494])).

tff(c_499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_497])).

tff(c_500,plain,
    ( ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_502,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_505,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_502])).

tff(c_508,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_505])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_508])).

tff(c_511,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_513,plain,(
    v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_511])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( ~ v2_struct_0(k8_tmap_1(A_18,B_19))
      | ~ m1_pre_topc(B_19,A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_516,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_513,c_34])).

tff(c_519,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_516])).

tff(c_521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_519])).

tff(c_523,plain,(
    ~ v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_511])).

tff(c_522,plain,(
    m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_511])).

tff(c_501,plain,(
    v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_512,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_36,plain,(
    ! [B_24,A_20,C_26] :
      ( r1_tmap_1(B_24,k8_tmap_1(A_20,B_24),k2_tmap_1(A_20,k8_tmap_1(A_20,B_24),k9_tmap_1(A_20,B_24),B_24),C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(B_24))
      | ~ m1_pre_topc(B_24,A_20)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_524,plain,(
    ! [B_205,A_206,C_207] :
      ( ~ r1_tmap_1(B_205,A_206,C_207,'#skF_1'(A_206,B_205,C_207))
      | v5_pre_topc(C_207,B_205,A_206)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_205),u1_struct_0(A_206))))
      | ~ v1_funct_2(C_207,u1_struct_0(B_205),u1_struct_0(A_206))
      | ~ v1_funct_1(C_207)
      | ~ l1_pre_topc(B_205)
      | ~ v2_pre_topc(B_205)
      | v2_struct_0(B_205)
      | ~ l1_pre_topc(A_206)
      | ~ v2_pre_topc(A_206)
      | v2_struct_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_655,plain,(
    ! [A_272,B_273] :
      ( v5_pre_topc(k2_tmap_1(A_272,k8_tmap_1(A_272,B_273),k9_tmap_1(A_272,B_273),B_273),B_273,k8_tmap_1(A_272,B_273))
      | ~ m1_subset_1(k2_tmap_1(A_272,k8_tmap_1(A_272,B_273),k9_tmap_1(A_272,B_273),B_273),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_273),u1_struct_0(k8_tmap_1(A_272,B_273)))))
      | ~ v1_funct_2(k2_tmap_1(A_272,k8_tmap_1(A_272,B_273),k9_tmap_1(A_272,B_273),B_273),u1_struct_0(B_273),u1_struct_0(k8_tmap_1(A_272,B_273)))
      | ~ v1_funct_1(k2_tmap_1(A_272,k8_tmap_1(A_272,B_273),k9_tmap_1(A_272,B_273),B_273))
      | ~ l1_pre_topc(B_273)
      | ~ v2_pre_topc(B_273)
      | ~ l1_pre_topc(k8_tmap_1(A_272,B_273))
      | ~ v2_pre_topc(k8_tmap_1(A_272,B_273))
      | v2_struct_0(k8_tmap_1(A_272,B_273))
      | ~ m1_subset_1('#skF_1'(k8_tmap_1(A_272,B_273),B_273,k2_tmap_1(A_272,k8_tmap_1(A_272,B_273),k9_tmap_1(A_272,B_273),B_273)),u1_struct_0(B_273))
      | ~ m1_pre_topc(B_273,A_272)
      | v2_struct_0(B_273)
      | ~ l1_pre_topc(A_272)
      | ~ v2_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(resolution,[status(thm)],[c_36,c_524])).

tff(c_660,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_305,c_655])).

tff(c_664,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_522,c_501,c_512,c_182,c_62,c_170,c_428,c_660])).

tff(c_666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_523,c_427,c_664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.64  
% 4.12/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.65  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 4.12/1.65  
% 4.12/1.65  %Foreground sorts:
% 4.12/1.65  
% 4.12/1.65  
% 4.12/1.65  %Background operators:
% 4.12/1.65  
% 4.12/1.65  
% 4.12/1.65  %Foreground operators:
% 4.12/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.12/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.12/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.12/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.65  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.12/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.12/1.65  tff(k9_tmap_1, type, k9_tmap_1: ($i * $i) > $i).
% 4.12/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.12/1.65  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 4.12/1.65  tff('#skF_2', type, '#skF_2': $i).
% 4.12/1.65  tff('#skF_3', type, '#skF_3': $i).
% 4.12/1.65  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.12/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.12/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.12/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.65  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.12/1.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.12/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.12/1.65  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.12/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.12/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.12/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.65  
% 4.12/1.68  tff(f_192, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (((v1_funct_1(k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), B)) & v1_funct_2(k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), B), u1_struct_0(B), u1_struct_0(k8_tmap_1(A, B)))) & v5_pre_topc(k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), B), B, k8_tmap_1(A, B))) & m1_subset_1(k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(k8_tmap_1(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_tmap_1)).
% 4.12/1.68  tff(f_92, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 4.12/1.68  tff(f_123, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((~v2_struct_0(k8_tmap_1(A, B)) & v1_pre_topc(k8_tmap_1(A, B))) & v2_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_tmap_1)).
% 4.12/1.68  tff(f_107, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k9_tmap_1(A, B)) & v1_funct_2(k9_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))) & m1_subset_1(k9_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 4.12/1.68  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.12/1.68  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.12/1.68  tff(f_77, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 4.12/1.68  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.12/1.68  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tmap_1)).
% 4.12/1.68  tff(f_141, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tmap_1(B, k8_tmap_1(A, B), k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), B), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_tmap_1)).
% 4.12/1.68  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.12/1.68  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.12/1.68  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.12/1.68  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.12/1.68  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.12/1.68  tff(c_18, plain, (![A_14, B_15]: (l1_pre_topc(k8_tmap_1(A_14, B_15)) | ~m1_pre_topc(B_15, A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.12/1.68  tff(c_30, plain, (![A_18, B_19]: (v2_pre_topc(k8_tmap_1(A_18, B_19)) | ~m1_pre_topc(B_19, A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.12/1.68  tff(c_28, plain, (![A_16, B_17]: (v1_funct_1(k9_tmap_1(A_16, B_17)) | ~m1_pre_topc(B_17, A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.12/1.68  tff(c_26, plain, (![A_16, B_17]: (v1_funct_2(k9_tmap_1(A_16, B_17), u1_struct_0(A_16), u1_struct_0(k8_tmap_1(A_16, B_17))) | ~m1_pre_topc(B_17, A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.12/1.68  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.12/1.68  tff(c_56, plain, (![B_51, A_52]: (l1_pre_topc(B_51) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.12/1.68  tff(c_59, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_56])).
% 4.12/1.68  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_59])).
% 4.12/1.68  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(k9_tmap_1(A_16, B_17), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16), u1_struct_0(k8_tmap_1(A_16, B_17))))) | ~m1_pre_topc(B_17, A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.12/1.68  tff(c_321, plain, (![A_158, B_159, C_160, D_161]: (v1_funct_2(k2_tmap_1(A_158, B_159, C_160, D_161), u1_struct_0(D_161), u1_struct_0(B_159)) | ~l1_struct_0(D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158), u1_struct_0(B_159)))) | ~v1_funct_2(C_160, u1_struct_0(A_158), u1_struct_0(B_159)) | ~v1_funct_1(C_160) | ~l1_struct_0(B_159) | ~l1_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.12/1.68  tff(c_361, plain, (![A_182, B_183, D_184]: (v1_funct_2(k2_tmap_1(A_182, k8_tmap_1(A_182, B_183), k9_tmap_1(A_182, B_183), D_184), u1_struct_0(D_184), u1_struct_0(k8_tmap_1(A_182, B_183))) | ~l1_struct_0(D_184) | ~v1_funct_2(k9_tmap_1(A_182, B_183), u1_struct_0(A_182), u1_struct_0(k8_tmap_1(A_182, B_183))) | ~v1_funct_1(k9_tmap_1(A_182, B_183)) | ~l1_struct_0(k8_tmap_1(A_182, B_183)) | ~l1_struct_0(A_182) | ~m1_pre_topc(B_183, A_182) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(resolution, [status(thm)], [c_24, c_321])).
% 4.12/1.68  tff(c_200, plain, (![A_133, B_134, C_135, D_136]: (m1_subset_1(k2_tmap_1(A_133, B_134, C_135, D_136), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_136), u1_struct_0(B_134)))) | ~l1_struct_0(D_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_133), u1_struct_0(B_134)))) | ~v1_funct_2(C_135, u1_struct_0(A_133), u1_struct_0(B_134)) | ~v1_funct_1(C_135) | ~l1_struct_0(B_134) | ~l1_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.12/1.68  tff(c_84, plain, (![A_71, B_72, C_73, D_74]: (v1_funct_1(k2_tmap_1(A_71, B_72, C_73, D_74)) | ~l1_struct_0(D_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71), u1_struct_0(B_72)))) | ~v1_funct_2(C_73, u1_struct_0(A_71), u1_struct_0(B_72)) | ~v1_funct_1(C_73) | ~l1_struct_0(B_72) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.12/1.68  tff(c_113, plain, (![A_96, B_97, D_98]: (v1_funct_1(k2_tmap_1(A_96, k8_tmap_1(A_96, B_97), k9_tmap_1(A_96, B_97), D_98)) | ~l1_struct_0(D_98) | ~v1_funct_2(k9_tmap_1(A_96, B_97), u1_struct_0(A_96), u1_struct_0(k8_tmap_1(A_96, B_97))) | ~v1_funct_1(k9_tmap_1(A_96, B_97)) | ~l1_struct_0(k8_tmap_1(A_96, B_97)) | ~l1_struct_0(A_96) | ~m1_pre_topc(B_97, A_96) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(resolution, [status(thm)], [c_24, c_84])).
% 4.12/1.68  tff(c_117, plain, (![A_99, B_100, D_101]: (v1_funct_1(k2_tmap_1(A_99, k8_tmap_1(A_99, B_100), k9_tmap_1(A_99, B_100), D_101)) | ~l1_struct_0(D_101) | ~v1_funct_1(k9_tmap_1(A_99, B_100)) | ~l1_struct_0(k8_tmap_1(A_99, B_100)) | ~l1_struct_0(A_99) | ~m1_pre_topc(B_100, A_99) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(resolution, [status(thm)], [c_26, c_113])).
% 4.12/1.68  tff(c_44, plain, (~m1_subset_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))))) | ~v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), '#skF_3', k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.12/1.68  tff(c_64, plain, (~v1_funct_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.12/1.68  tff(c_120, plain, (~l1_struct_0('#skF_3') | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_117, c_64])).
% 4.12/1.68  tff(c_123, plain, (~l1_struct_0('#skF_3') | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_120])).
% 4.12/1.68  tff(c_124, plain, (~l1_struct_0('#skF_3') | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_123])).
% 4.12/1.68  tff(c_125, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_124])).
% 4.12/1.68  tff(c_128, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_125])).
% 4.12/1.68  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_128])).
% 4.12/1.68  tff(c_133, plain, (~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_124])).
% 4.12/1.68  tff(c_135, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_133])).
% 4.12/1.68  tff(c_138, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_135])).
% 4.12/1.68  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_138])).
% 4.12/1.68  tff(c_143, plain, (~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_133])).
% 4.12/1.68  tff(c_146, plain, (~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_143])).
% 4.12/1.68  tff(c_150, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_146])).
% 4.12/1.68  tff(c_153, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_150])).
% 4.12/1.68  tff(c_156, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_153])).
% 4.12/1.68  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_156])).
% 4.12/1.68  tff(c_159, plain, (~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_143])).
% 4.12/1.68  tff(c_163, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_159])).
% 4.12/1.68  tff(c_166, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_163])).
% 4.12/1.68  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_166])).
% 4.12/1.68  tff(c_169, plain, (~v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), '#skF_3', k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))))), inference(splitRight, [status(thm)], [c_44])).
% 4.12/1.68  tff(c_186, plain, (~m1_subset_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))))), inference(splitLeft, [status(thm)], [c_169])).
% 4.12/1.68  tff(c_210, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1(k9_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))))) | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_200, c_186])).
% 4.12/1.68  tff(c_211, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_210])).
% 4.12/1.68  tff(c_214, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_211])).
% 4.12/1.68  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_214])).
% 4.12/1.68  tff(c_219, plain, (~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~m1_subset_1(k9_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))))) | ~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_210])).
% 4.12/1.68  tff(c_221, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_219])).
% 4.12/1.68  tff(c_224, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_221])).
% 4.12/1.68  tff(c_228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_224])).
% 4.12/1.68  tff(c_229, plain, (~m1_subset_1(k9_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))))) | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_219])).
% 4.12/1.68  tff(c_238, plain, (~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_229])).
% 4.12/1.68  tff(c_242, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_238])).
% 4.12/1.68  tff(c_245, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_242])).
% 4.12/1.68  tff(c_248, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_245])).
% 4.12/1.68  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_248])).
% 4.12/1.68  tff(c_251, plain, (~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~m1_subset_1(k9_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))))), inference(splitRight, [status(thm)], [c_229])).
% 4.12/1.68  tff(c_253, plain, (~m1_subset_1(k9_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))))), inference(splitLeft, [status(thm)], [c_251])).
% 4.12/1.68  tff(c_256, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_253])).
% 4.12/1.68  tff(c_259, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_256])).
% 4.12/1.68  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_259])).
% 4.12/1.68  tff(c_262, plain, (~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_251])).
% 4.12/1.68  tff(c_280, plain, (~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_262])).
% 4.12/1.68  tff(c_283, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_280])).
% 4.12/1.68  tff(c_286, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_283])).
% 4.12/1.68  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_286])).
% 4.12/1.68  tff(c_289, plain, (~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_262])).
% 4.12/1.68  tff(c_298, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_289])).
% 4.12/1.68  tff(c_301, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_298])).
% 4.12/1.68  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_301])).
% 4.12/1.68  tff(c_304, plain, (~v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), '#skF_3', k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_169])).
% 4.12/1.68  tff(c_320, plain, (~v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_304])).
% 4.12/1.68  tff(c_364, plain, (~l1_struct_0('#skF_3') | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_361, c_320])).
% 4.12/1.68  tff(c_367, plain, (~l1_struct_0('#skF_3') | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_364])).
% 4.12/1.68  tff(c_368, plain, (~l1_struct_0('#skF_3') | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_367])).
% 4.12/1.68  tff(c_369, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_368])).
% 4.12/1.68  tff(c_372, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_369])).
% 4.12/1.68  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_372])).
% 4.12/1.68  tff(c_377, plain, (~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_368])).
% 4.12/1.68  tff(c_379, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_377])).
% 4.12/1.68  tff(c_382, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_379])).
% 4.12/1.68  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_382])).
% 4.12/1.68  tff(c_387, plain, (~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_377])).
% 4.12/1.68  tff(c_389, plain, (~l1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_387])).
% 4.12/1.68  tff(c_393, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_389])).
% 4.12/1.68  tff(c_396, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_393])).
% 4.12/1.68  tff(c_399, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_396])).
% 4.12/1.68  tff(c_401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_399])).
% 4.12/1.68  tff(c_402, plain, (~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_387])).
% 4.12/1.68  tff(c_408, plain, (~v1_funct_2(k9_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_402])).
% 4.12/1.68  tff(c_411, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_408])).
% 4.12/1.68  tff(c_414, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_411])).
% 4.12/1.68  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_414])).
% 4.12/1.68  tff(c_417, plain, (~v1_funct_1(k9_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_402])).
% 4.12/1.68  tff(c_421, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_417])).
% 4.12/1.68  tff(c_424, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_421])).
% 4.12/1.68  tff(c_426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_424])).
% 4.12/1.68  tff(c_427, plain, (~v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), '#skF_3', k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_304])).
% 4.12/1.68  tff(c_176, plain, (![B_106, A_107]: (v2_pre_topc(B_106) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.12/1.68  tff(c_179, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_176])).
% 4.12/1.68  tff(c_182, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_179])).
% 4.12/1.68  tff(c_170, plain, (v1_funct_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 4.12/1.68  tff(c_428, plain, (v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_304])).
% 4.12/1.68  tff(c_305, plain, (m1_subset_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')))))), inference(splitRight, [status(thm)], [c_169])).
% 4.12/1.68  tff(c_473, plain, (![A_199, B_200, C_201]: (m1_subset_1('#skF_1'(A_199, B_200, C_201), u1_struct_0(B_200)) | v5_pre_topc(C_201, B_200, A_199) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_200), u1_struct_0(A_199)))) | ~v1_funct_2(C_201, u1_struct_0(B_200), u1_struct_0(A_199)) | ~v1_funct_1(C_201) | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.12/1.68  tff(c_479, plain, (m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_3', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3')), u1_struct_0('#skF_3')) | v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), '#skF_3', k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_305, c_473])).
% 4.12/1.68  tff(c_484, plain, (m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_3', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3')), u1_struct_0('#skF_3')) | v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), '#skF_3', k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_62, c_170, c_428, c_479])).
% 4.12/1.68  tff(c_485, plain, (m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_3', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3')), u1_struct_0('#skF_3')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_427, c_484])).
% 4.12/1.68  tff(c_486, plain, (~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_485])).
% 4.12/1.68  tff(c_494, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_486])).
% 4.12/1.68  tff(c_497, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_494])).
% 4.12/1.68  tff(c_499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_497])).
% 4.12/1.68  tff(c_500, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_3', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3')), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_485])).
% 4.12/1.68  tff(c_502, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_500])).
% 4.12/1.68  tff(c_505, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_502])).
% 4.12/1.68  tff(c_508, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_505])).
% 4.12/1.68  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_508])).
% 4.12/1.68  tff(c_511, plain, (m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_3', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3')), u1_struct_0('#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_500])).
% 4.12/1.68  tff(c_513, plain, (v2_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_511])).
% 4.12/1.68  tff(c_34, plain, (![A_18, B_19]: (~v2_struct_0(k8_tmap_1(A_18, B_19)) | ~m1_pre_topc(B_19, A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.12/1.68  tff(c_516, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_513, c_34])).
% 4.12/1.68  tff(c_519, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_516])).
% 4.12/1.68  tff(c_521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_519])).
% 4.12/1.68  tff(c_523, plain, (~v2_struct_0(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_511])).
% 4.12/1.68  tff(c_522, plain, (m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_3', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3')), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_511])).
% 4.12/1.68  tff(c_501, plain, (v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_485])).
% 4.12/1.68  tff(c_512, plain, (l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_500])).
% 4.12/1.68  tff(c_36, plain, (![B_24, A_20, C_26]: (r1_tmap_1(B_24, k8_tmap_1(A_20, B_24), k2_tmap_1(A_20, k8_tmap_1(A_20, B_24), k9_tmap_1(A_20, B_24), B_24), C_26) | ~m1_subset_1(C_26, u1_struct_0(B_24)) | ~m1_pre_topc(B_24, A_20) | v2_struct_0(B_24) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.12/1.68  tff(c_524, plain, (![B_205, A_206, C_207]: (~r1_tmap_1(B_205, A_206, C_207, '#skF_1'(A_206, B_205, C_207)) | v5_pre_topc(C_207, B_205, A_206) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_205), u1_struct_0(A_206)))) | ~v1_funct_2(C_207, u1_struct_0(B_205), u1_struct_0(A_206)) | ~v1_funct_1(C_207) | ~l1_pre_topc(B_205) | ~v2_pre_topc(B_205) | v2_struct_0(B_205) | ~l1_pre_topc(A_206) | ~v2_pre_topc(A_206) | v2_struct_0(A_206))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.12/1.68  tff(c_655, plain, (![A_272, B_273]: (v5_pre_topc(k2_tmap_1(A_272, k8_tmap_1(A_272, B_273), k9_tmap_1(A_272, B_273), B_273), B_273, k8_tmap_1(A_272, B_273)) | ~m1_subset_1(k2_tmap_1(A_272, k8_tmap_1(A_272, B_273), k9_tmap_1(A_272, B_273), B_273), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_273), u1_struct_0(k8_tmap_1(A_272, B_273))))) | ~v1_funct_2(k2_tmap_1(A_272, k8_tmap_1(A_272, B_273), k9_tmap_1(A_272, B_273), B_273), u1_struct_0(B_273), u1_struct_0(k8_tmap_1(A_272, B_273))) | ~v1_funct_1(k2_tmap_1(A_272, k8_tmap_1(A_272, B_273), k9_tmap_1(A_272, B_273), B_273)) | ~l1_pre_topc(B_273) | ~v2_pre_topc(B_273) | ~l1_pre_topc(k8_tmap_1(A_272, B_273)) | ~v2_pre_topc(k8_tmap_1(A_272, B_273)) | v2_struct_0(k8_tmap_1(A_272, B_273)) | ~m1_subset_1('#skF_1'(k8_tmap_1(A_272, B_273), B_273, k2_tmap_1(A_272, k8_tmap_1(A_272, B_273), k9_tmap_1(A_272, B_273), B_273)), u1_struct_0(B_273)) | ~m1_pre_topc(B_273, A_272) | v2_struct_0(B_273) | ~l1_pre_topc(A_272) | ~v2_pre_topc(A_272) | v2_struct_0(A_272))), inference(resolution, [status(thm)], [c_36, c_524])).
% 4.12/1.68  tff(c_660, plain, (v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), '#skF_3', k8_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'(k8_tmap_1('#skF_2', '#skF_3'), '#skF_3', k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3')), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_305, c_655])).
% 4.12/1.68  tff(c_664, plain, (v5_pre_topc(k2_tmap_1('#skF_2', k8_tmap_1('#skF_2', '#skF_3'), k9_tmap_1('#skF_2', '#skF_3'), '#skF_3'), '#skF_3', k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_522, c_501, c_512, c_182, c_62, c_170, c_428, c_660])).
% 4.12/1.68  tff(c_666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_523, c_427, c_664])).
% 4.12/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.68  
% 4.12/1.68  Inference rules
% 4.12/1.68  ----------------------
% 4.12/1.68  #Ref     : 0
% 4.12/1.68  #Sup     : 98
% 4.12/1.68  #Fact    : 0
% 4.12/1.68  #Define  : 0
% 4.12/1.68  #Split   : 20
% 4.12/1.68  #Chain   : 0
% 4.12/1.68  #Close   : 0
% 4.12/1.68  
% 4.12/1.68  Ordering : KBO
% 4.12/1.68  
% 4.12/1.68  Simplification rules
% 4.12/1.68  ----------------------
% 4.12/1.68  #Subsume      : 17
% 4.12/1.68  #Demod        : 141
% 4.12/1.68  #Tautology    : 4
% 4.12/1.68  #SimpNegUnit  : 25
% 4.12/1.68  #BackRed      : 0
% 4.12/1.68  
% 4.12/1.68  #Partial instantiations: 0
% 4.12/1.68  #Strategies tried      : 1
% 4.12/1.68  
% 4.12/1.68  Timing (in seconds)
% 4.12/1.68  ----------------------
% 4.12/1.68  Preprocessing        : 0.35
% 4.12/1.68  Parsing              : 0.19
% 4.12/1.68  CNF conversion       : 0.03
% 4.12/1.68  Main loop            : 0.53
% 4.12/1.68  Inferencing          : 0.22
% 4.12/1.68  Reduction            : 0.14
% 4.12/1.68  Demodulation         : 0.10
% 4.12/1.68  BG Simplification    : 0.03
% 4.12/1.68  Subsumption          : 0.11
% 4.12/1.68  Abstraction          : 0.02
% 4.12/1.68  MUC search           : 0.00
% 4.12/1.68  Cooper               : 0.00
% 4.12/1.68  Total                : 0.94
% 4.12/1.68  Index Insertion      : 0.00
% 4.12/1.68  Index Deletion       : 0.00
% 4.12/1.68  Index Matching       : 0.00
% 4.12/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
