%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1804+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:26 EST 2020

% Result     : Theorem 6.45s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :  251 (1932 expanded)
%              Number of leaves         :   45 ( 594 expanded)
%              Depth                    :   17
%              Number of atoms          :  655 (8892 expanded)
%              Number of equality atoms :   10 ( 164 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r2_hidden > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k9_tmap_1 > k8_tmap_1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_1 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_tmap_1,type,(
    k9_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_240,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_tmap_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( ~ v2_struct_0(k8_tmap_1(A,B))
        & v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tmap_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k9_tmap_1(A,B))
        & v1_funct_2(k9_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
        & m1_subset_1(k9_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_71,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_203,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

tff(f_174,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_tmap_1)).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_74,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_68,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( l1_pre_topc(k8_tmap_1(A_15,B_16))
      | ~ m1_pre_topc(B_16,A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    ! [A_24,B_25] :
      ( v2_pre_topc(k8_tmap_1(A_24,B_25))
      | ~ m1_pre_topc(B_25,A_24)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( v1_funct_1(k9_tmap_1(A_17,B_18))
      | ~ m1_pre_topc(B_18,A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( v1_funct_2(k9_tmap_1(A_17,B_18),u1_struct_0(A_17),u1_struct_0(k8_tmap_1(A_17,B_18)))
      | ~ m1_pre_topc(B_18,A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_390,plain,(
    ! [B_215,A_216] :
      ( v2_pre_topc(B_215)
      | ~ m1_pre_topc(B_215,A_216)
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_396,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_390])).

tff(c_402,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_396])).

tff(c_360,plain,(
    ! [B_203,A_204] :
      ( l1_pre_topc(B_203)
      | ~ m1_pre_topc(B_203,A_204)
      | ~ l1_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_366,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_360])).

tff(c_372,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_366])).

tff(c_79,plain,(
    ! [B_77,A_78] :
      ( l1_pre_topc(B_77)
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_85,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_79])).

tff(c_91,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_85])).

tff(c_82,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_79])).

tff(c_88,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_82])).

tff(c_62,plain,(
    r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_122,plain,(
    ! [B_91,A_92] :
      ( r1_tsep_1(B_91,A_92)
      | ~ r1_tsep_1(A_92,B_91)
      | ~ l1_struct_0(B_91)
      | ~ l1_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_125,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_122])).

tff(c_141,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_144,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_141])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_144])).

tff(c_149,plain,
    ( ~ l1_struct_0('#skF_5')
    | r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_151,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_154,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_151])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_154])).

tff(c_160,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k9_tmap_1(A_17,B_18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_17),u1_struct_0(k8_tmap_1(A_17,B_18)))))
      | ~ m1_pre_topc(B_18,A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_196,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( v1_funct_1(k2_tmap_1(A_127,B_128,C_129,D_130))
      | ~ l1_struct_0(D_130)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_127),u1_struct_0(B_128))))
      | ~ v1_funct_2(C_129,u1_struct_0(A_127),u1_struct_0(B_128))
      | ~ v1_funct_1(C_129)
      | ~ l1_struct_0(B_128)
      | ~ l1_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_301,plain,(
    ! [A_191,B_192,D_193] :
      ( v1_funct_1(k2_tmap_1(A_191,k8_tmap_1(A_191,B_192),k9_tmap_1(A_191,B_192),D_193))
      | ~ l1_struct_0(D_193)
      | ~ v1_funct_2(k9_tmap_1(A_191,B_192),u1_struct_0(A_191),u1_struct_0(k8_tmap_1(A_191,B_192)))
      | ~ v1_funct_1(k9_tmap_1(A_191,B_192))
      | ~ l1_struct_0(k8_tmap_1(A_191,B_192))
      | ~ l1_struct_0(A_191)
      | ~ m1_pre_topc(B_192,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_26,c_196])).

tff(c_305,plain,(
    ! [A_194,B_195,D_196] :
      ( v1_funct_1(k2_tmap_1(A_194,k8_tmap_1(A_194,B_195),k9_tmap_1(A_194,B_195),D_196))
      | ~ l1_struct_0(D_196)
      | ~ v1_funct_1(k9_tmap_1(A_194,B_195))
      | ~ l1_struct_0(k8_tmap_1(A_194,B_195))
      | ~ l1_struct_0(A_194)
      | ~ m1_pre_topc(B_195,A_194)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(resolution,[status(thm)],[c_28,c_301])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_77,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_308,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_305,c_77])).

tff(c_311,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_160,c_308])).

tff(c_312,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_311])).

tff(c_313,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_316,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_313])).

tff(c_320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_316])).

tff(c_321,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_334,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_321])).

tff(c_337,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_334])).

tff(c_340,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_337])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_340])).

tff(c_343,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_348,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_343])).

tff(c_351,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_348])).

tff(c_354,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_351])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_354])).

tff(c_358,plain,(
    v1_funct_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_363,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_360])).

tff(c_369,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_363])).

tff(c_403,plain,(
    ! [B_217,A_218] :
      ( r1_tsep_1(B_217,A_218)
      | ~ r1_tsep_1(A_218,B_217)
      | ~ l1_struct_0(B_217)
      | ~ l1_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_406,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_403])).

tff(c_407,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_410,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_407])).

tff(c_414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_410])).

tff(c_415,plain,
    ( ~ l1_struct_0('#skF_5')
    | r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_418,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_415])).

tff(c_421,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_418])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_421])).

tff(c_427,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_527,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( m1_subset_1(k2_tmap_1(A_283,B_284,C_285,D_286),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_286),u1_struct_0(B_284))))
      | ~ l1_struct_0(D_286)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_283),u1_struct_0(B_284))))
      | ~ v1_funct_2(C_285,u1_struct_0(A_283),u1_struct_0(B_284))
      | ~ v1_funct_1(C_285)
      | ~ l1_struct_0(B_284)
      | ~ l1_struct_0(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_357,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v5_pre_topc(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_417,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))))) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_540,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_527,c_417])).

tff(c_550,plain,
    ( ~ m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_540])).

tff(c_552,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_550])).

tff(c_555,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_552])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_555])).

tff(c_560,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))))) ),
    inference(splitRight,[status(thm)],[c_550])).

tff(c_562,plain,(
    ~ m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))))) ),
    inference(splitLeft,[status(thm)],[c_560])).

tff(c_565,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_562])).

tff(c_568,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_565])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_568])).

tff(c_572,plain,(
    m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))))) ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( v1_funct_1(k2_partfun1(A_7,B_8,C_9,D_10))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_593,plain,(
    ! [D_10] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k9_tmap_1('#skF_3','#skF_4'),D_10))
      | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_572,c_12])).

tff(c_597,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_593])).

tff(c_600,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_597])).

tff(c_603,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_600])).

tff(c_605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_603])).

tff(c_607,plain,(
    v1_funct_1(k9_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_593])).

tff(c_571,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_608,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_571])).

tff(c_612,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_608])).

tff(c_615,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_612])).

tff(c_618,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_615])).

tff(c_620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_618])).

tff(c_621,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_655,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_621])).

tff(c_658,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_655])).

tff(c_661,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_658])).

tff(c_663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_661])).

tff(c_665,plain,(
    m1_subset_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))))) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_711,plain,(
    ! [A_313,B_314,C_315,D_316] :
      ( k2_partfun1(A_313,B_314,C_315,D_316) = k7_relat_1(C_315,D_316)
      | ~ m1_subset_1(C_315,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314)))
      | ~ v1_funct_1(C_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_713,plain,(
    ! [D_316] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_316) = k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_316)
      | ~ v1_funct_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_665,c_711])).

tff(c_716,plain,(
    ! [D_316] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_316) = k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_316) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_713])).

tff(c_705,plain,(
    ! [A_309,B_310,C_311,D_312] :
      ( v1_funct_1(k2_partfun1(A_309,B_310,C_311,D_312))
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310)))
      | ~ v1_funct_1(C_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_707,plain,(
    ! [D_312] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_312))
      | ~ v1_funct_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_665,c_705])).

tff(c_710,plain,(
    ! [D_312] : v1_funct_1(k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_312)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_707])).

tff(c_771,plain,(
    ! [D_312] : v1_funct_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_312)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_710])).

tff(c_772,plain,(
    ! [D_348] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348) = k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_713])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( m1_subset_1(k2_partfun1(A_7,B_8,C_9,D_10),k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_780,plain,(
    ! [D_348] :
      ( m1_subset_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
      | ~ m1_subset_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
      | ~ v1_funct_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_10])).

tff(c_788,plain,(
    ! [D_348] : m1_subset_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_665,c_780])).

tff(c_995,plain,(
    ! [A_403,B_404,C_405] :
      ( m1_subset_1('#skF_2'(A_403,B_404,C_405),u1_struct_0(B_404))
      | v5_pre_topc(C_405,B_404,A_403)
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_404),u1_struct_0(A_403))))
      | ~ v1_funct_2(C_405,u1_struct_0(B_404),u1_struct_0(A_403))
      | ~ v1_funct_1(C_405)
      | ~ l1_pre_topc(B_404)
      | ~ v2_pre_topc(B_404)
      | v2_struct_0(B_404)
      | ~ l1_pre_topc(A_403)
      | ~ v2_pre_topc(A_403)
      | v2_struct_0(A_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1001,plain,(
    ! [D_348] :
      ( m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348)),u1_struct_0('#skF_5'))
      | v5_pre_topc(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
      | ~ v1_funct_2(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_788,c_995])).

tff(c_1016,plain,(
    ! [D_348] :
      ( m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348)),u1_struct_0('#skF_5'))
      | v5_pre_topc(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
      | ~ v1_funct_2(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_372,c_771,c_1001])).

tff(c_1017,plain,(
    ! [D_348] :
      ( m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348)),u1_struct_0('#skF_5'))
      | v5_pre_topc(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
      | ~ v1_funct_2(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_348),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1016])).

tff(c_1024,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1017])).

tff(c_1027,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1024])).

tff(c_1030,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_1027])).

tff(c_1032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1030])).

tff(c_1034,plain,(
    v2_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1017])).

tff(c_717,plain,(
    ! [A_317,B_318,C_319,D_320] :
      ( m1_subset_1(k2_partfun1(A_317,B_318,C_319,D_320),k1_zfmisc_1(k2_zfmisc_1(A_317,B_318)))
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_317,B_318)))
      | ~ v1_funct_1(C_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( k2_partfun1(A_26,B_27,C_28,D_29) = k7_relat_1(C_28,D_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_834,plain,(
    ! [D_357,B_356,A_359,D_360,C_358] :
      ( k2_partfun1(A_359,B_356,k2_partfun1(A_359,B_356,C_358,D_360),D_357) = k7_relat_1(k2_partfun1(A_359,B_356,C_358,D_360),D_357)
      | ~ v1_funct_1(k2_partfun1(A_359,B_356,C_358,D_360))
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_359,B_356)))
      | ~ v1_funct_1(C_358) ) ),
    inference(resolution,[status(thm)],[c_717,c_46])).

tff(c_840,plain,(
    ! [D_316,D_357] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_316),D_357) = k7_relat_1(k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_316),D_357)
      | ~ v1_funct_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_316))
      | ~ m1_subset_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
      | ~ v1_funct_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_716,c_834])).

tff(c_847,plain,(
    ! [D_316,D_357] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_316),D_357) = k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_316),D_357) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_665,c_771,c_716,c_716,c_840])).

tff(c_743,plain,(
    ! [D_335,A_337,B_334,D_338,C_336] :
      ( v1_funct_1(k2_partfun1(A_337,B_334,k2_partfun1(A_337,B_334,C_336,D_338),D_335))
      | ~ v1_funct_1(k2_partfun1(A_337,B_334,C_336,D_338))
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_337,B_334)))
      | ~ v1_funct_1(C_336) ) ),
    inference(resolution,[status(thm)],[c_717,c_12])).

tff(c_749,plain,(
    ! [D_338,D_335] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_338),D_335))
      | ~ v1_funct_1(k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_338))
      | ~ v1_funct_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_665,c_743])).

tff(c_754,plain,(
    ! [D_338,D_335] : v1_funct_1(k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_338),D_335)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_710,c_749])).

tff(c_770,plain,(
    ! [D_338,D_335] : v1_funct_1(k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_338),D_335)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_754])).

tff(c_868,plain,(
    ! [D_338,D_335] : v1_funct_1(k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_338),D_335)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_770])).

tff(c_869,plain,(
    ! [D_368,D_369] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369) = k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_665,c_771,c_716,c_716,c_840])).

tff(c_879,plain,(
    ! [D_368,D_369] :
      ( m1_subset_1(k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
      | ~ m1_subset_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
      | ~ v1_funct_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_10])).

tff(c_889,plain,(
    ! [D_368,D_369] : m1_subset_1(k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_788,c_879])).

tff(c_999,plain,(
    ! [D_368,D_369] :
      ( m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369)),u1_struct_0('#skF_5'))
      | v5_pre_topc(k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
      | ~ v1_funct_2(k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_889,c_995])).

tff(c_1012,plain,(
    ! [D_368,D_369] :
      ( m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369)),u1_struct_0('#skF_5'))
      | v5_pre_topc(k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
      | ~ v1_funct_2(k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_372,c_868,c_999])).

tff(c_1013,plain,(
    ! [D_368,D_369] :
      ( m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369)),u1_struct_0('#skF_5'))
      | v5_pre_topc(k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
      | ~ v1_funct_2(k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1012])).

tff(c_1076,plain,(
    ! [D_368,D_369] :
      ( m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369)),u1_struct_0('#skF_5'))
      | v5_pre_topc(k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
      | ~ v1_funct_2(k7_relat_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_368),D_369),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
      | v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_1013])).

tff(c_1077,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1076])).

tff(c_1084,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1077])).

tff(c_1087,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_1084])).

tff(c_1089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1087])).

tff(c_1091,plain,(
    l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1076])).

tff(c_666,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_415])).

tff(c_669,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_666])).

tff(c_673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_669])).

tff(c_675,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_791,plain,(
    ! [D_350] : m1_subset_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_350),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_665,c_780])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( v1_funct_1(k2_tmap_1(A_11,B_12,C_13,D_14))
      | ~ l1_struct_0(D_14)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_11),u1_struct_0(B_12))))
      | ~ v1_funct_2(C_13,u1_struct_0(A_11),u1_struct_0(B_12))
      | ~ v1_funct_1(C_13)
      | ~ l1_struct_0(B_12)
      | ~ l1_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_793,plain,(
    ! [D_350,D_14] :
      ( v1_funct_1(k2_tmap_1('#skF_5',k8_tmap_1('#skF_3','#skF_4'),k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_350),D_14))
      | ~ l1_struct_0(D_14)
      | ~ v1_funct_2(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_350),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | ~ v1_funct_1(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_350))
      | ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4'))
      | ~ l1_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_791,c_18])).

tff(c_804,plain,(
    ! [D_350,D_14] :
      ( v1_funct_1(k2_tmap_1('#skF_5',k8_tmap_1('#skF_3','#skF_4'),k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_350),D_14))
      | ~ l1_struct_0(D_14)
      | ~ v1_funct_2(k7_relat_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),D_350),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_771,c_793])).

tff(c_1074,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_804])).

tff(c_1095,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_1074])).

tff(c_1097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1091,c_1095])).

tff(c_1099,plain,(
    l1_struct_0(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_804])).

tff(c_849,plain,(
    ! [A_361,B_362,C_363,D_364] :
      ( v1_funct_2(k2_tmap_1(A_361,B_362,C_363,D_364),u1_struct_0(D_364),u1_struct_0(B_362))
      | ~ l1_struct_0(D_364)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361),u1_struct_0(B_362))))
      | ~ v1_funct_2(C_363,u1_struct_0(A_361),u1_struct_0(B_362))
      | ~ v1_funct_1(C_363)
      | ~ l1_struct_0(B_362)
      | ~ l1_struct_0(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1176,plain,(
    ! [A_442,B_443,D_444] :
      ( v1_funct_2(k2_tmap_1(A_442,k8_tmap_1(A_442,B_443),k9_tmap_1(A_442,B_443),D_444),u1_struct_0(D_444),u1_struct_0(k8_tmap_1(A_442,B_443)))
      | ~ l1_struct_0(D_444)
      | ~ v1_funct_2(k9_tmap_1(A_442,B_443),u1_struct_0(A_442),u1_struct_0(k8_tmap_1(A_442,B_443)))
      | ~ v1_funct_1(k9_tmap_1(A_442,B_443))
      | ~ l1_struct_0(k8_tmap_1(A_442,B_443))
      | ~ l1_struct_0(A_442)
      | ~ m1_pre_topc(B_443,A_442)
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(resolution,[status(thm)],[c_26,c_849])).

tff(c_664,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_731,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_1179,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1176,c_731])).

tff(c_1182,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_1099,c_675,c_1179])).

tff(c_1183,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1182])).

tff(c_1184,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1183])).

tff(c_1187,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1184])).

tff(c_1191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1187])).

tff(c_1192,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1183])).

tff(c_1194,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1192])).

tff(c_1197,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1194])).

tff(c_1200,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_1197])).

tff(c_1202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1200])).

tff(c_1203,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1192])).

tff(c_1207,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1203])).

tff(c_1210,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_1207])).

tff(c_1212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1210])).

tff(c_1213,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_1214,plain,(
    v1_funct_2(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_1504,plain,(
    ! [A_528,B_529,C_530] :
      ( m1_subset_1('#skF_2'(A_528,B_529,C_530),u1_struct_0(B_529))
      | v5_pre_topc(C_530,B_529,A_528)
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_529),u1_struct_0(A_528))))
      | ~ v1_funct_2(C_530,u1_struct_0(B_529),u1_struct_0(A_528))
      | ~ v1_funct_1(C_530)
      | ~ l1_pre_topc(B_529)
      | ~ v2_pre_topc(B_529)
      | v2_struct_0(B_529)
      | ~ l1_pre_topc(A_528)
      | ~ v2_pre_topc(A_528)
      | v2_struct_0(A_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1517,plain,
    ( m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')),u1_struct_0('#skF_5'))
    | v5_pre_topc(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_665,c_1504])).

tff(c_1531,plain,
    ( m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')),u1_struct_0('#skF_5'))
    | v5_pre_topc(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_372,c_358,c_1214,c_1517])).

tff(c_1532,plain,
    ( m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')),u1_struct_0('#skF_5'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1213,c_1531])).

tff(c_1533,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1532])).

tff(c_1536,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1533])).

tff(c_1539,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_1536])).

tff(c_1541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1539])).

tff(c_1542,plain,
    ( ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1532])).

tff(c_1544,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1542])).

tff(c_1552,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1544])).

tff(c_1555,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_1552])).

tff(c_1557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1555])).

tff(c_1558,plain,
    ( m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')),u1_struct_0('#skF_5'))
    | v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1542])).

tff(c_1560,plain,(
    v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1558])).

tff(c_44,plain,(
    ! [A_24,B_25] :
      ( ~ v2_struct_0(k8_tmap_1(A_24,B_25))
      | ~ m1_pre_topc(B_25,A_24)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1566,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1560,c_44])).

tff(c_1569,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_1566])).

tff(c_1571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1569])).

tff(c_1573,plain,(
    ~ v2_struct_0(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1558])).

tff(c_1572,plain,(
    m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1558])).

tff(c_1543,plain,(
    v2_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1532])).

tff(c_1559,plain,(
    l1_pre_topc(k8_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1542])).

tff(c_50,plain,(
    ! [C_44,A_32,B_40,D_46] :
      ( r1_tmap_1(C_44,k8_tmap_1(A_32,B_40),k2_tmap_1(A_32,k8_tmap_1(A_32,B_40),k9_tmap_1(A_32,B_40),C_44),D_46)
      | ~ m1_subset_1(D_46,u1_struct_0(C_44))
      | ~ r1_tsep_1(B_40,C_44)
      | ~ m1_pre_topc(C_44,A_32)
      | v2_struct_0(C_44)
      | ~ m1_pre_topc(B_40,A_32)
      | v2_struct_0(B_40)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1574,plain,(
    ! [B_534,A_535,C_536] :
      ( ~ r1_tmap_1(B_534,A_535,C_536,'#skF_2'(A_535,B_534,C_536))
      | v5_pre_topc(C_536,B_534,A_535)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_534),u1_struct_0(A_535))))
      | ~ v1_funct_2(C_536,u1_struct_0(B_534),u1_struct_0(A_535))
      | ~ v1_funct_1(C_536)
      | ~ l1_pre_topc(B_534)
      | ~ v2_pre_topc(B_534)
      | v2_struct_0(B_534)
      | ~ l1_pre_topc(A_535)
      | ~ v2_pre_topc(A_535)
      | v2_struct_0(A_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_2544,plain,(
    ! [A_880,B_881,C_882] :
      ( v5_pre_topc(k2_tmap_1(A_880,k8_tmap_1(A_880,B_881),k9_tmap_1(A_880,B_881),C_882),C_882,k8_tmap_1(A_880,B_881))
      | ~ m1_subset_1(k2_tmap_1(A_880,k8_tmap_1(A_880,B_881),k9_tmap_1(A_880,B_881),C_882),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_882),u1_struct_0(k8_tmap_1(A_880,B_881)))))
      | ~ v1_funct_2(k2_tmap_1(A_880,k8_tmap_1(A_880,B_881),k9_tmap_1(A_880,B_881),C_882),u1_struct_0(C_882),u1_struct_0(k8_tmap_1(A_880,B_881)))
      | ~ v1_funct_1(k2_tmap_1(A_880,k8_tmap_1(A_880,B_881),k9_tmap_1(A_880,B_881),C_882))
      | ~ l1_pre_topc(C_882)
      | ~ v2_pre_topc(C_882)
      | ~ l1_pre_topc(k8_tmap_1(A_880,B_881))
      | ~ v2_pre_topc(k8_tmap_1(A_880,B_881))
      | v2_struct_0(k8_tmap_1(A_880,B_881))
      | ~ m1_subset_1('#skF_2'(k8_tmap_1(A_880,B_881),C_882,k2_tmap_1(A_880,k8_tmap_1(A_880,B_881),k9_tmap_1(A_880,B_881),C_882)),u1_struct_0(C_882))
      | ~ r1_tsep_1(B_881,C_882)
      | ~ m1_pre_topc(C_882,A_880)
      | v2_struct_0(C_882)
      | ~ m1_pre_topc(B_881,A_880)
      | v2_struct_0(B_881)
      | ~ l1_pre_topc(A_880)
      | ~ v2_pre_topc(A_880)
      | v2_struct_0(A_880) ) ),
    inference(resolution,[status(thm)],[c_50,c_1574])).

tff(c_2549,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_2'(k8_tmap_1('#skF_3','#skF_4'),'#skF_5',k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5')),u1_struct_0('#skF_5'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_665,c_2544])).

tff(c_2553,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0(k8_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_64,c_62,c_1572,c_1543,c_1559,c_402,c_372,c_358,c_1214,c_2549])).

tff(c_2555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_66,c_1573,c_1213,c_2553])).

%------------------------------------------------------------------------------
