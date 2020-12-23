%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:08 EST 2020

% Result     : Theorem 7.30s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  325 (2115 expanded)
%              Number of leaves         :   29 ( 852 expanded)
%              Depth                    :   14
%              Number of atoms          : 1599 (25166 expanded)
%              Number of equality atoms :  148 (1210 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r4_tsep_1,type,(
    r4_tsep_1: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

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

tff(f_211,negated_conjecture,(
    ~ ! [A] :
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
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( A = k1_tsep_1(A,D,E)
                            & r4_tsep_1(A,D,E) )
                         => ( ( v1_funct_1(C)
                              & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                              & v5_pre_topc(C,A,B)
                              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                          <=> ( v1_funct_1(k2_tmap_1(A,B,C,D))
                              & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
                              & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B)
                              & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B))))
                              & v1_funct_1(k2_tmap_1(A,B,C,E))
                              & v1_funct_2(k2_tmap_1(A,B,C,E),u1_struct_0(E),u1_struct_0(B))
                              & v5_pre_topc(k2_tmap_1(A,B,C,E),E,B)
                              & m1_subset_1(k2_tmap_1(A,B,C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_52,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_144,axiom,(
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
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( r4_tsep_1(A,C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                       => ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                            & v5_pre_topc(E,k1_tsep_1(A,C,D),B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E))
                            & v1_funct_2(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),u1_struct_0(C),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),C,B)
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
                            & v1_funct_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E))
                            & v1_funct_2(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),D,B)
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_146,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_186,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_136,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_190,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_126,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_188,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_116,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_193,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_106,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_187,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_96,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_191,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_86,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_189,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_76,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_192,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_160,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_170,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_160])).

tff(c_180,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_170])).

tff(c_833,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_190,c_188,c_193,c_187,c_191,c_189,c_192,c_180])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_30,plain,(
    ! [A_78] :
      ( m1_pre_topc(A_78,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_36,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_223,plain,(
    ! [B_111,C_114,A_115,D_113,E_112] :
      ( k3_tmap_1(A_115,B_111,C_114,D_113,E_112) = k2_partfun1(u1_struct_0(C_114),u1_struct_0(B_111),E_112,u1_struct_0(D_113))
      | ~ m1_pre_topc(D_113,C_114)
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_114),u1_struct_0(B_111))))
      | ~ v1_funct_2(E_112,u1_struct_0(C_114),u1_struct_0(B_111))
      | ~ v1_funct_1(E_112)
      | ~ m1_pre_topc(D_113,A_115)
      | ~ m1_pre_topc(C_114,A_115)
      | ~ l1_pre_topc(B_111)
      | ~ v2_pre_topc(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_229,plain,(
    ! [A_115,D_113] :
      ( k3_tmap_1(A_115,'#skF_2','#skF_1',D_113,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_113))
      | ~ m1_pre_topc(D_113,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_113,A_115)
      | ~ m1_pre_topc('#skF_1',A_115)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_44,c_223])).

tff(c_240,plain,(
    ! [A_115,D_113] :
      ( k3_tmap_1(A_115,'#skF_2','#skF_1',D_113,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_113))
      | ~ m1_pre_topc(D_113,'#skF_1')
      | ~ m1_pre_topc(D_113,A_115)
      | ~ m1_pre_topc('#skF_1',A_115)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_229])).

tff(c_243,plain,(
    ! [A_116,D_117] :
      ( k3_tmap_1(A_116,'#skF_2','#skF_1',D_117,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_117))
      | ~ m1_pre_topc(D_117,'#skF_1')
      | ~ m1_pre_topc(D_117,A_116)
      | ~ m1_pre_topc('#skF_1',A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_240])).

tff(c_247,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_243])).

tff(c_253,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_36,c_247])).

tff(c_254,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_253])).

tff(c_259,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_262,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_259])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_262])).

tff(c_268,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_249,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_243])).

tff(c_257,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_249])).

tff(c_258,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_257])).

tff(c_332,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_258])).

tff(c_194,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k2_partfun1(u1_struct_0(A_106),u1_struct_0(B_107),C_108,u1_struct_0(D_109)) = k2_tmap_1(A_106,B_107,C_108,D_109)
      | ~ m1_pre_topc(D_109,A_106)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_106),u1_struct_0(B_107))))
      | ~ v1_funct_2(C_108,u1_struct_0(A_106),u1_struct_0(B_107))
      | ~ v1_funct_1(C_108)
      | ~ l1_pre_topc(B_107)
      | ~ v2_pre_topc(B_107)
      | v2_struct_0(B_107)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_200,plain,(
    ! [D_109] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_109)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_109)
      | ~ m1_pre_topc(D_109,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_194])).

tff(c_211,plain,(
    ! [D_109] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_109)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_109)
      | ~ m1_pre_topc(D_109,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_200])).

tff(c_212,plain,(
    ! [D_109] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_109)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_109)
      | ~ m1_pre_topc(D_109,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_211])).

tff(c_336,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_212])).

tff(c_343,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_336])).

tff(c_267,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_278,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_212])).

tff(c_285,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_278])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_32,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_34,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_874,plain,(
    ! [E_205,A_202,C_204,B_203,D_206] :
      ( v5_pre_topc(E_205,k1_tsep_1(A_202,C_204,D_206),B_203)
      | ~ m1_subset_1(k3_tmap_1(A_202,B_203,k1_tsep_1(A_202,C_204,D_206),D_206,E_205),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_206),u1_struct_0(B_203))))
      | ~ v5_pre_topc(k3_tmap_1(A_202,B_203,k1_tsep_1(A_202,C_204,D_206),D_206,E_205),D_206,B_203)
      | ~ v1_funct_2(k3_tmap_1(A_202,B_203,k1_tsep_1(A_202,C_204,D_206),D_206,E_205),u1_struct_0(D_206),u1_struct_0(B_203))
      | ~ v1_funct_1(k3_tmap_1(A_202,B_203,k1_tsep_1(A_202,C_204,D_206),D_206,E_205))
      | ~ m1_subset_1(k3_tmap_1(A_202,B_203,k1_tsep_1(A_202,C_204,D_206),C_204,E_205),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_204),u1_struct_0(B_203))))
      | ~ v5_pre_topc(k3_tmap_1(A_202,B_203,k1_tsep_1(A_202,C_204,D_206),C_204,E_205),C_204,B_203)
      | ~ v1_funct_2(k3_tmap_1(A_202,B_203,k1_tsep_1(A_202,C_204,D_206),C_204,E_205),u1_struct_0(C_204),u1_struct_0(B_203))
      | ~ v1_funct_1(k3_tmap_1(A_202,B_203,k1_tsep_1(A_202,C_204,D_206),C_204,E_205))
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_202,C_204,D_206)),u1_struct_0(B_203))))
      | ~ v1_funct_2(E_205,u1_struct_0(k1_tsep_1(A_202,C_204,D_206)),u1_struct_0(B_203))
      | ~ v1_funct_1(E_205)
      | ~ r4_tsep_1(A_202,C_204,D_206)
      | ~ m1_pre_topc(D_206,A_202)
      | v2_struct_0(D_206)
      | ~ m1_pre_topc(C_204,A_202)
      | v2_struct_0(C_204)
      | ~ l1_pre_topc(B_203)
      | ~ v2_pre_topc(B_203)
      | v2_struct_0(B_203)
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_881,plain,(
    ! [E_205,B_203] :
      ( v5_pre_topc(E_205,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_203)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_203,'#skF_1','#skF_5',E_205),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_203))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_203,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_205),'#skF_5',B_203)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_203,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_205),u1_struct_0('#skF_5'),u1_struct_0(B_203))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_203,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_205))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_203,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_205),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_203))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_203,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_205),'#skF_4',B_203)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_203,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_205),u1_struct_0('#skF_4'),u1_struct_0(B_203))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_203,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_205))
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_203))))
      | ~ v1_funct_2(E_205,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_203))
      | ~ v1_funct_1(E_205)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_203)
      | ~ v2_pre_topc(B_203)
      | v2_struct_0(B_203)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_874])).

tff(c_885,plain,(
    ! [E_205,B_203] :
      ( v5_pre_topc(E_205,'#skF_1',B_203)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_203,'#skF_1','#skF_5',E_205),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_203))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_203,'#skF_1','#skF_5',E_205),'#skF_5',B_203)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_203,'#skF_1','#skF_5',E_205),u1_struct_0('#skF_5'),u1_struct_0(B_203))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_203,'#skF_1','#skF_5',E_205))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_203,'#skF_1','#skF_4',E_205),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_203))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_203,'#skF_1','#skF_4',E_205),'#skF_4',B_203)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_203,'#skF_1','#skF_4',E_205),u1_struct_0('#skF_4'),u1_struct_0(B_203))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_203,'#skF_1','#skF_4',E_205))
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_203))))
      | ~ v1_funct_2(E_205,u1_struct_0('#skF_1'),u1_struct_0(B_203))
      | ~ v1_funct_1(E_205)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_203)
      | ~ v2_pre_topc(B_203)
      | v2_struct_0(B_203)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_36,c_32,c_34,c_34,c_34,c_34,c_34,c_34,c_34,c_34,c_34,c_34,c_881])).

tff(c_889,plain,(
    ! [E_215,B_216] :
      ( v5_pre_topc(E_215,'#skF_1',B_216)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_216,'#skF_1','#skF_5',E_215),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_216))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_216,'#skF_1','#skF_5',E_215),'#skF_5',B_216)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_216,'#skF_1','#skF_5',E_215),u1_struct_0('#skF_5'),u1_struct_0(B_216))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_216,'#skF_1','#skF_5',E_215))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_216,'#skF_1','#skF_4',E_215),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_216))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_216,'#skF_1','#skF_4',E_215),'#skF_4',B_216)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_216,'#skF_1','#skF_4',E_215),u1_struct_0('#skF_4'),u1_struct_0(B_216))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_216,'#skF_1','#skF_4',E_215))
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_216))))
      | ~ v1_funct_2(E_215,u1_struct_0('#skF_1'),u1_struct_0(B_216))
      | ~ v1_funct_1(E_215)
      | ~ l1_pre_topc(B_216)
      | ~ v2_pre_topc(B_216)
      | v2_struct_0(B_216) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_42,c_38,c_885])).

tff(c_895,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_889])).

tff(c_898,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_186,c_343,c_190,c_343,c_188,c_343,c_193,c_343,c_187,c_285,c_191,c_285,c_189,c_285,c_192,c_895])).

tff(c_900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_833,c_898])).

tff(c_902,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_901,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_926,plain,(
    ! [B_222,C_225,E_223,D_224,A_226] :
      ( k3_tmap_1(A_226,B_222,C_225,D_224,E_223) = k2_partfun1(u1_struct_0(C_225),u1_struct_0(B_222),E_223,u1_struct_0(D_224))
      | ~ m1_pre_topc(D_224,C_225)
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_225),u1_struct_0(B_222))))
      | ~ v1_funct_2(E_223,u1_struct_0(C_225),u1_struct_0(B_222))
      | ~ v1_funct_1(E_223)
      | ~ m1_pre_topc(D_224,A_226)
      | ~ m1_pre_topc(C_225,A_226)
      | ~ l1_pre_topc(B_222)
      | ~ v2_pre_topc(B_222)
      | v2_struct_0(B_222)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_930,plain,(
    ! [A_226,D_224] :
      ( k3_tmap_1(A_226,'#skF_2','#skF_1',D_224,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_224))
      | ~ m1_pre_topc(D_224,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_224,A_226)
      | ~ m1_pre_topc('#skF_1',A_226)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_44,c_926])).

tff(c_937,plain,(
    ! [A_226,D_224] :
      ( k3_tmap_1(A_226,'#skF_2','#skF_1',D_224,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_224))
      | ~ m1_pre_topc(D_224,'#skF_1')
      | ~ m1_pre_topc(D_224,A_226)
      | ~ m1_pre_topc('#skF_1',A_226)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_930])).

tff(c_939,plain,(
    ! [A_227,D_228] :
      ( k3_tmap_1(A_227,'#skF_2','#skF_1',D_228,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_228))
      | ~ m1_pre_topc(D_228,'#skF_1')
      | ~ m1_pre_topc(D_228,A_227)
      | ~ m1_pre_topc('#skF_1',A_227)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_937])).

tff(c_943,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_939])).

tff(c_949,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_36,c_943])).

tff(c_950,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_949])).

tff(c_955,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_950])).

tff(c_959,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_955])).

tff(c_963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_959])).

tff(c_965,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_950])).

tff(c_945,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_939])).

tff(c_953,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_945])).

tff(c_954,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_953])).

tff(c_1034,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_954])).

tff(c_903,plain,(
    ! [A_217,B_218,C_219,D_220] :
      ( k2_partfun1(u1_struct_0(A_217),u1_struct_0(B_218),C_219,u1_struct_0(D_220)) = k2_tmap_1(A_217,B_218,C_219,D_220)
      | ~ m1_pre_topc(D_220,A_217)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_217),u1_struct_0(B_218))))
      | ~ v1_funct_2(C_219,u1_struct_0(A_217),u1_struct_0(B_218))
      | ~ v1_funct_1(C_219)
      | ~ l1_pre_topc(B_218)
      | ~ v2_pre_topc(B_218)
      | v2_struct_0(B_218)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_907,plain,(
    ! [D_220] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_220)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_220)
      | ~ m1_pre_topc(D_220,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_903])).

tff(c_914,plain,(
    ! [D_220] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_220)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_220)
      | ~ m1_pre_topc(D_220,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_907])).

tff(c_915,plain,(
    ! [D_220] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_220)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_220)
      | ~ m1_pre_topc(D_220,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_914])).

tff(c_1038,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1034,c_915])).

tff(c_1045,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1038])).

tff(c_1295,plain,(
    ! [C_278,D_280,A_276,B_277,E_279] :
      ( m1_subset_1(k3_tmap_1(A_276,B_277,k1_tsep_1(A_276,C_278,D_280),C_278,E_279),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_278),u1_struct_0(B_277))))
      | ~ v5_pre_topc(E_279,k1_tsep_1(A_276,C_278,D_280),B_277)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_276,C_278,D_280)),u1_struct_0(B_277))))
      | ~ v1_funct_2(E_279,u1_struct_0(k1_tsep_1(A_276,C_278,D_280)),u1_struct_0(B_277))
      | ~ v1_funct_1(E_279)
      | ~ r4_tsep_1(A_276,C_278,D_280)
      | ~ m1_pre_topc(D_280,A_276)
      | v2_struct_0(D_280)
      | ~ m1_pre_topc(C_278,A_276)
      | v2_struct_0(C_278)
      | ~ l1_pre_topc(B_277)
      | ~ v2_pre_topc(B_277)
      | v2_struct_0(B_277)
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276)
      | v2_struct_0(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1337,plain,(
    ! [B_277,E_279] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_277,'#skF_1','#skF_4',E_279),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_277))))
      | ~ v5_pre_topc(E_279,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_277)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_277))))
      | ~ v1_funct_2(E_279,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_277))
      | ~ v1_funct_1(E_279)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_277)
      | ~ v2_pre_topc(B_277)
      | v2_struct_0(B_277)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1295])).

tff(c_1362,plain,(
    ! [B_277,E_279] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_277,'#skF_1','#skF_4',E_279),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_277))))
      | ~ v5_pre_topc(E_279,'#skF_1',B_277)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_277))))
      | ~ v1_funct_2(E_279,u1_struct_0('#skF_1'),u1_struct_0(B_277))
      | ~ v1_funct_1(E_279)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_277)
      | ~ v2_pre_topc(B_277)
      | v2_struct_0(B_277)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_36,c_32,c_34,c_34,c_34,c_1337])).

tff(c_1377,plain,(
    ! [B_283,E_284] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_283,'#skF_1','#skF_4',E_284),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_283))))
      | ~ v5_pre_topc(E_284,'#skF_1',B_283)
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_283))))
      | ~ v1_funct_2(E_284,u1_struct_0('#skF_1'),u1_struct_0(B_283))
      | ~ v1_funct_1(E_284)
      | ~ l1_pre_topc(B_283)
      | ~ v2_pre_topc(B_283)
      | v2_struct_0(B_283) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_42,c_38,c_1362])).

tff(c_1384,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_1377])).

tff(c_1389,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_901,c_1384])).

tff(c_1391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_902,c_1389])).

tff(c_1393,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1392,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1411,plain,(
    ! [C_293,A_294,B_290,E_291,D_292] :
      ( k3_tmap_1(A_294,B_290,C_293,D_292,E_291) = k2_partfun1(u1_struct_0(C_293),u1_struct_0(B_290),E_291,u1_struct_0(D_292))
      | ~ m1_pre_topc(D_292,C_293)
      | ~ m1_subset_1(E_291,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_293),u1_struct_0(B_290))))
      | ~ v1_funct_2(E_291,u1_struct_0(C_293),u1_struct_0(B_290))
      | ~ v1_funct_1(E_291)
      | ~ m1_pre_topc(D_292,A_294)
      | ~ m1_pre_topc(C_293,A_294)
      | ~ l1_pre_topc(B_290)
      | ~ v2_pre_topc(B_290)
      | v2_struct_0(B_290)
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1413,plain,(
    ! [A_294,D_292] :
      ( k3_tmap_1(A_294,'#skF_2','#skF_1',D_292,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_292))
      | ~ m1_pre_topc(D_292,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_292,A_294)
      | ~ m1_pre_topc('#skF_1',A_294)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(resolution,[status(thm)],[c_44,c_1411])).

tff(c_1416,plain,(
    ! [A_294,D_292] :
      ( k3_tmap_1(A_294,'#skF_2','#skF_1',D_292,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_292))
      | ~ m1_pre_topc(D_292,'#skF_1')
      | ~ m1_pre_topc(D_292,A_294)
      | ~ m1_pre_topc('#skF_1',A_294)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1413])).

tff(c_1418,plain,(
    ! [A_295,D_296] :
      ( k3_tmap_1(A_295,'#skF_2','#skF_1',D_296,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_296))
      | ~ m1_pre_topc(D_296,'#skF_1')
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc('#skF_1',A_295)
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1416])).

tff(c_1422,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1418])).

tff(c_1428,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_36,c_1422])).

tff(c_1429,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1428])).

tff(c_1440,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1429])).

tff(c_1443,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1440])).

tff(c_1447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1443])).

tff(c_1448,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1429])).

tff(c_1395,plain,(
    ! [A_285,B_286,C_287,D_288] :
      ( k2_partfun1(u1_struct_0(A_285),u1_struct_0(B_286),C_287,u1_struct_0(D_288)) = k2_tmap_1(A_285,B_286,C_287,D_288)
      | ~ m1_pre_topc(D_288,A_285)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_285),u1_struct_0(B_286))))
      | ~ v1_funct_2(C_287,u1_struct_0(A_285),u1_struct_0(B_286))
      | ~ v1_funct_1(C_287)
      | ~ l1_pre_topc(B_286)
      | ~ v2_pre_topc(B_286)
      | v2_struct_0(B_286)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1397,plain,(
    ! [D_288] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_288)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_288)
      | ~ m1_pre_topc(D_288,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_1395])).

tff(c_1400,plain,(
    ! [D_288] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_288)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_288)
      | ~ m1_pre_topc(D_288,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_1397])).

tff(c_1401,plain,(
    ! [D_288] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_288)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_288)
      | ~ m1_pre_topc(D_288,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_1400])).

tff(c_1495,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1448,c_1401])).

tff(c_1502,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1495])).

tff(c_1807,plain,(
    ! [D_350,A_346,B_347,E_349,C_348] :
      ( m1_subset_1(k3_tmap_1(A_346,B_347,k1_tsep_1(A_346,C_348,D_350),D_350,E_349),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_350),u1_struct_0(B_347))))
      | ~ v5_pre_topc(E_349,k1_tsep_1(A_346,C_348,D_350),B_347)
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_346,C_348,D_350)),u1_struct_0(B_347))))
      | ~ v1_funct_2(E_349,u1_struct_0(k1_tsep_1(A_346,C_348,D_350)),u1_struct_0(B_347))
      | ~ v1_funct_1(E_349)
      | ~ r4_tsep_1(A_346,C_348,D_350)
      | ~ m1_pre_topc(D_350,A_346)
      | v2_struct_0(D_350)
      | ~ m1_pre_topc(C_348,A_346)
      | v2_struct_0(C_348)
      | ~ l1_pre_topc(B_347)
      | ~ v2_pre_topc(B_347)
      | v2_struct_0(B_347)
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1852,plain,(
    ! [B_347,E_349] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_347,'#skF_1','#skF_5',E_349),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_347))))
      | ~ v5_pre_topc(E_349,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_347)
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_347))))
      | ~ v1_funct_2(E_349,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_347))
      | ~ v1_funct_1(E_349)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_347)
      | ~ v2_pre_topc(B_347)
      | v2_struct_0(B_347)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1807])).

tff(c_1880,plain,(
    ! [B_347,E_349] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_347,'#skF_1','#skF_5',E_349),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_347))))
      | ~ v5_pre_topc(E_349,'#skF_1',B_347)
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_347))))
      | ~ v1_funct_2(E_349,u1_struct_0('#skF_1'),u1_struct_0(B_347))
      | ~ v1_funct_1(E_349)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_347)
      | ~ v2_pre_topc(B_347)
      | v2_struct_0(B_347)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_36,c_32,c_34,c_34,c_34,c_1852])).

tff(c_1923,plain,(
    ! [B_355,E_356] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_355,'#skF_1','#skF_5',E_356),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_355))))
      | ~ v5_pre_topc(E_356,'#skF_1',B_355)
      | ~ m1_subset_1(E_356,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_355))))
      | ~ v1_funct_2(E_356,u1_struct_0('#skF_1'),u1_struct_0(B_355))
      | ~ v1_funct_1(E_356)
      | ~ l1_pre_topc(B_355)
      | ~ v2_pre_topc(B_355)
      | v2_struct_0(B_355) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_42,c_38,c_1880])).

tff(c_1930,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1502,c_1923])).

tff(c_1935,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_1392,c_1930])).

tff(c_1937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1393,c_1935])).

tff(c_1939,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1938,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1949,plain,(
    ! [C_364,B_361,D_363,A_365,E_362] :
      ( k3_tmap_1(A_365,B_361,C_364,D_363,E_362) = k2_partfun1(u1_struct_0(C_364),u1_struct_0(B_361),E_362,u1_struct_0(D_363))
      | ~ m1_pre_topc(D_363,C_364)
      | ~ m1_subset_1(E_362,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_364),u1_struct_0(B_361))))
      | ~ v1_funct_2(E_362,u1_struct_0(C_364),u1_struct_0(B_361))
      | ~ v1_funct_1(E_362)
      | ~ m1_pre_topc(D_363,A_365)
      | ~ m1_pre_topc(C_364,A_365)
      | ~ l1_pre_topc(B_361)
      | ~ v2_pre_topc(B_361)
      | v2_struct_0(B_361)
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1951,plain,(
    ! [A_365,D_363] :
      ( k3_tmap_1(A_365,'#skF_2','#skF_1',D_363,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_363))
      | ~ m1_pre_topc(D_363,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_363,A_365)
      | ~ m1_pre_topc('#skF_1',A_365)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(resolution,[status(thm)],[c_44,c_1949])).

tff(c_1954,plain,(
    ! [A_365,D_363] :
      ( k3_tmap_1(A_365,'#skF_2','#skF_1',D_363,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_363))
      | ~ m1_pre_topc(D_363,'#skF_1')
      | ~ m1_pre_topc(D_363,A_365)
      | ~ m1_pre_topc('#skF_1',A_365)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1951])).

tff(c_1965,plain,(
    ! [A_367,D_368] :
      ( k3_tmap_1(A_367,'#skF_2','#skF_1',D_368,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_368))
      | ~ m1_pre_topc(D_368,'#skF_1')
      | ~ m1_pre_topc(D_368,A_367)
      | ~ m1_pre_topc('#skF_1',A_367)
      | ~ l1_pre_topc(A_367)
      | ~ v2_pre_topc(A_367)
      | v2_struct_0(A_367) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1954])).

tff(c_1969,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1965])).

tff(c_1975,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_36,c_1969])).

tff(c_1976,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1975])).

tff(c_1981,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1976])).

tff(c_1985,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1981])).

tff(c_1989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1985])).

tff(c_1990,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1976])).

tff(c_1942,plain,(
    ! [A_357,B_358,C_359,D_360] :
      ( k2_partfun1(u1_struct_0(A_357),u1_struct_0(B_358),C_359,u1_struct_0(D_360)) = k2_tmap_1(A_357,B_358,C_359,D_360)
      | ~ m1_pre_topc(D_360,A_357)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_357),u1_struct_0(B_358))))
      | ~ v1_funct_2(C_359,u1_struct_0(A_357),u1_struct_0(B_358))
      | ~ v1_funct_1(C_359)
      | ~ l1_pre_topc(B_358)
      | ~ v2_pre_topc(B_358)
      | v2_struct_0(B_358)
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357)
      | v2_struct_0(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1944,plain,(
    ! [D_360] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_360)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_360)
      | ~ m1_pre_topc(D_360,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_1942])).

tff(c_1947,plain,(
    ! [D_360] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_360)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_360)
      | ~ m1_pre_topc(D_360,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_1944])).

tff(c_1948,plain,(
    ! [D_360] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_360)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_360)
      | ~ m1_pre_topc(D_360,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_1947])).

tff(c_2001,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1990,c_1948])).

tff(c_2008,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2001])).

tff(c_2264,plain,(
    ! [C_408,E_409,B_407,D_410,A_406] :
      ( v1_funct_2(k3_tmap_1(A_406,B_407,k1_tsep_1(A_406,C_408,D_410),D_410,E_409),u1_struct_0(D_410),u1_struct_0(B_407))
      | ~ v5_pre_topc(E_409,k1_tsep_1(A_406,C_408,D_410),B_407)
      | ~ m1_subset_1(E_409,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_406,C_408,D_410)),u1_struct_0(B_407))))
      | ~ v1_funct_2(E_409,u1_struct_0(k1_tsep_1(A_406,C_408,D_410)),u1_struct_0(B_407))
      | ~ v1_funct_1(E_409)
      | ~ r4_tsep_1(A_406,C_408,D_410)
      | ~ m1_pre_topc(D_410,A_406)
      | v2_struct_0(D_410)
      | ~ m1_pre_topc(C_408,A_406)
      | v2_struct_0(C_408)
      | ~ l1_pre_topc(B_407)
      | ~ v2_pre_topc(B_407)
      | v2_struct_0(B_407)
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2266,plain,(
    ! [B_407,E_409] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_407,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_409),u1_struct_0('#skF_5'),u1_struct_0(B_407))
      | ~ v5_pre_topc(E_409,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_407)
      | ~ m1_subset_1(E_409,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_407))))
      | ~ v1_funct_2(E_409,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_407))
      | ~ v1_funct_1(E_409)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_407)
      | ~ v2_pre_topc(B_407)
      | v2_struct_0(B_407)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2264])).

tff(c_2268,plain,(
    ! [B_407,E_409] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_407,'#skF_1','#skF_5',E_409),u1_struct_0('#skF_5'),u1_struct_0(B_407))
      | ~ v5_pre_topc(E_409,'#skF_1',B_407)
      | ~ m1_subset_1(E_409,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_407))))
      | ~ v1_funct_2(E_409,u1_struct_0('#skF_1'),u1_struct_0(B_407))
      | ~ v1_funct_1(E_409)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_407)
      | ~ v2_pre_topc(B_407)
      | v2_struct_0(B_407)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_36,c_32,c_34,c_34,c_34,c_2266])).

tff(c_2339,plain,(
    ! [B_416,E_417] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_416,'#skF_1','#skF_5',E_417),u1_struct_0('#skF_5'),u1_struct_0(B_416))
      | ~ v5_pre_topc(E_417,'#skF_1',B_416)
      | ~ m1_subset_1(E_417,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_416))))
      | ~ v1_funct_2(E_417,u1_struct_0('#skF_1'),u1_struct_0(B_416))
      | ~ v1_funct_1(E_417)
      | ~ l1_pre_topc(B_416)
      | ~ v2_pre_topc(B_416)
      | v2_struct_0(B_416) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_42,c_38,c_2268])).

tff(c_2344,plain,
    ( v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_2339])).

tff(c_2350,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_1938,c_2008,c_2344])).

tff(c_2352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1939,c_2350])).

tff(c_2354,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_2353,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_2374,plain,(
    ! [A_427,E_424,D_425,C_426,B_423] :
      ( k3_tmap_1(A_427,B_423,C_426,D_425,E_424) = k2_partfun1(u1_struct_0(C_426),u1_struct_0(B_423),E_424,u1_struct_0(D_425))
      | ~ m1_pre_topc(D_425,C_426)
      | ~ m1_subset_1(E_424,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_426),u1_struct_0(B_423))))
      | ~ v1_funct_2(E_424,u1_struct_0(C_426),u1_struct_0(B_423))
      | ~ v1_funct_1(E_424)
      | ~ m1_pre_topc(D_425,A_427)
      | ~ m1_pre_topc(C_426,A_427)
      | ~ l1_pre_topc(B_423)
      | ~ v2_pre_topc(B_423)
      | v2_struct_0(B_423)
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2376,plain,(
    ! [A_427,D_425] :
      ( k3_tmap_1(A_427,'#skF_2','#skF_1',D_425,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_425))
      | ~ m1_pre_topc(D_425,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_425,A_427)
      | ~ m1_pre_topc('#skF_1',A_427)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(resolution,[status(thm)],[c_44,c_2374])).

tff(c_2379,plain,(
    ! [A_427,D_425] :
      ( k3_tmap_1(A_427,'#skF_2','#skF_1',D_425,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_425))
      | ~ m1_pre_topc(D_425,'#skF_1')
      | ~ m1_pre_topc(D_425,A_427)
      | ~ m1_pre_topc('#skF_1',A_427)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_2376])).

tff(c_2387,plain,(
    ! [A_433,D_434] :
      ( k3_tmap_1(A_433,'#skF_2','#skF_1',D_434,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_434))
      | ~ m1_pre_topc(D_434,'#skF_1')
      | ~ m1_pre_topc(D_434,A_433)
      | ~ m1_pre_topc('#skF_1',A_433)
      | ~ l1_pre_topc(A_433)
      | ~ v2_pre_topc(A_433)
      | v2_struct_0(A_433) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2379])).

tff(c_2391,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2387])).

tff(c_2397,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_36,c_2391])).

tff(c_2398,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2397])).

tff(c_2403,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2398])).

tff(c_2406,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2403])).

tff(c_2410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2406])).

tff(c_2412,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2398])).

tff(c_2393,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2387])).

tff(c_2401,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_2393])).

tff(c_2402,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2401])).

tff(c_2413,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2402])).

tff(c_2421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_2413])).

tff(c_2422,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2402])).

tff(c_2358,plain,(
    ! [A_418,B_419,C_420,D_421] :
      ( k2_partfun1(u1_struct_0(A_418),u1_struct_0(B_419),C_420,u1_struct_0(D_421)) = k2_tmap_1(A_418,B_419,C_420,D_421)
      | ~ m1_pre_topc(D_421,A_418)
      | ~ m1_subset_1(C_420,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_418),u1_struct_0(B_419))))
      | ~ v1_funct_2(C_420,u1_struct_0(A_418),u1_struct_0(B_419))
      | ~ v1_funct_1(C_420)
      | ~ l1_pre_topc(B_419)
      | ~ v2_pre_topc(B_419)
      | v2_struct_0(B_419)
      | ~ l1_pre_topc(A_418)
      | ~ v2_pre_topc(A_418)
      | v2_struct_0(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2360,plain,(
    ! [D_421] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_421)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_421)
      | ~ m1_pre_topc(D_421,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_2358])).

tff(c_2363,plain,(
    ! [D_421] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_421)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_421)
      | ~ m1_pre_topc(D_421,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_2360])).

tff(c_2364,plain,(
    ! [D_421] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_421)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_421)
      | ~ m1_pre_topc(D_421,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_2363])).

tff(c_2434,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2422,c_2364])).

tff(c_2441,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2434])).

tff(c_2674,plain,(
    ! [A_460,D_464,B_461,E_463,C_462] :
      ( v1_funct_2(k3_tmap_1(A_460,B_461,k1_tsep_1(A_460,C_462,D_464),C_462,E_463),u1_struct_0(C_462),u1_struct_0(B_461))
      | ~ v5_pre_topc(E_463,k1_tsep_1(A_460,C_462,D_464),B_461)
      | ~ m1_subset_1(E_463,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_460,C_462,D_464)),u1_struct_0(B_461))))
      | ~ v1_funct_2(E_463,u1_struct_0(k1_tsep_1(A_460,C_462,D_464)),u1_struct_0(B_461))
      | ~ v1_funct_1(E_463)
      | ~ r4_tsep_1(A_460,C_462,D_464)
      | ~ m1_pre_topc(D_464,A_460)
      | v2_struct_0(D_464)
      | ~ m1_pre_topc(C_462,A_460)
      | v2_struct_0(C_462)
      | ~ l1_pre_topc(B_461)
      | ~ v2_pre_topc(B_461)
      | v2_struct_0(B_461)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2676,plain,(
    ! [B_461,E_463] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_461,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_463),u1_struct_0('#skF_4'),u1_struct_0(B_461))
      | ~ v5_pre_topc(E_463,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_461)
      | ~ m1_subset_1(E_463,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_461))))
      | ~ v1_funct_2(E_463,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_461))
      | ~ v1_funct_1(E_463)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_461)
      | ~ v2_pre_topc(B_461)
      | v2_struct_0(B_461)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2674])).

tff(c_2678,plain,(
    ! [B_461,E_463] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_461,'#skF_1','#skF_4',E_463),u1_struct_0('#skF_4'),u1_struct_0(B_461))
      | ~ v5_pre_topc(E_463,'#skF_1',B_461)
      | ~ m1_subset_1(E_463,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_461))))
      | ~ v1_funct_2(E_463,u1_struct_0('#skF_1'),u1_struct_0(B_461))
      | ~ v1_funct_1(E_463)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_461)
      | ~ v2_pre_topc(B_461)
      | v2_struct_0(B_461)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_36,c_32,c_34,c_34,c_34,c_2676])).

tff(c_2680,plain,(
    ! [B_465,E_466] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_465,'#skF_1','#skF_4',E_466),u1_struct_0('#skF_4'),u1_struct_0(B_465))
      | ~ v5_pre_topc(E_466,'#skF_1',B_465)
      | ~ m1_subset_1(E_466,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_465))))
      | ~ v1_funct_2(E_466,u1_struct_0('#skF_1'),u1_struct_0(B_465))
      | ~ v1_funct_1(E_466)
      | ~ l1_pre_topc(B_465)
      | ~ v2_pre_topc(B_465)
      | v2_struct_0(B_465) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_42,c_38,c_2678])).

tff(c_2682,plain,
    ( v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_2680])).

tff(c_2685,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_2353,c_2441,c_2682])).

tff(c_2687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2354,c_2685])).

tff(c_2689,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_2688,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_2710,plain,(
    ! [A_476,B_472,D_474,E_473,C_475] :
      ( k3_tmap_1(A_476,B_472,C_475,D_474,E_473) = k2_partfun1(u1_struct_0(C_475),u1_struct_0(B_472),E_473,u1_struct_0(D_474))
      | ~ m1_pre_topc(D_474,C_475)
      | ~ m1_subset_1(E_473,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_475),u1_struct_0(B_472))))
      | ~ v1_funct_2(E_473,u1_struct_0(C_475),u1_struct_0(B_472))
      | ~ v1_funct_1(E_473)
      | ~ m1_pre_topc(D_474,A_476)
      | ~ m1_pre_topc(C_475,A_476)
      | ~ l1_pre_topc(B_472)
      | ~ v2_pre_topc(B_472)
      | v2_struct_0(B_472)
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2712,plain,(
    ! [A_476,D_474] :
      ( k3_tmap_1(A_476,'#skF_2','#skF_1',D_474,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_474))
      | ~ m1_pre_topc(D_474,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_474,A_476)
      | ~ m1_pre_topc('#skF_1',A_476)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(resolution,[status(thm)],[c_44,c_2710])).

tff(c_2715,plain,(
    ! [A_476,D_474] :
      ( k3_tmap_1(A_476,'#skF_2','#skF_1',D_474,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_474))
      | ~ m1_pre_topc(D_474,'#skF_1')
      | ~ m1_pre_topc(D_474,A_476)
      | ~ m1_pre_topc('#skF_1',A_476)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_2712])).

tff(c_2717,plain,(
    ! [A_477,D_478] :
      ( k3_tmap_1(A_477,'#skF_2','#skF_1',D_478,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_478))
      | ~ m1_pre_topc(D_478,'#skF_1')
      | ~ m1_pre_topc(D_478,A_477)
      | ~ m1_pre_topc('#skF_1',A_477)
      | ~ l1_pre_topc(A_477)
      | ~ v2_pre_topc(A_477)
      | v2_struct_0(A_477) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2715])).

tff(c_2721,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2717])).

tff(c_2727,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_36,c_2721])).

tff(c_2728,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2727])).

tff(c_2733,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2728])).

tff(c_2742,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2733])).

tff(c_2746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2742])).

tff(c_2747,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2728])).

tff(c_2694,plain,(
    ! [A_467,B_468,C_469,D_470] :
      ( k2_partfun1(u1_struct_0(A_467),u1_struct_0(B_468),C_469,u1_struct_0(D_470)) = k2_tmap_1(A_467,B_468,C_469,D_470)
      | ~ m1_pre_topc(D_470,A_467)
      | ~ m1_subset_1(C_469,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_467),u1_struct_0(B_468))))
      | ~ v1_funct_2(C_469,u1_struct_0(A_467),u1_struct_0(B_468))
      | ~ v1_funct_1(C_469)
      | ~ l1_pre_topc(B_468)
      | ~ v2_pre_topc(B_468)
      | v2_struct_0(B_468)
      | ~ l1_pre_topc(A_467)
      | ~ v2_pre_topc(A_467)
      | v2_struct_0(A_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2696,plain,(
    ! [D_470] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_470)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_470)
      | ~ m1_pre_topc(D_470,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_2694])).

tff(c_2699,plain,(
    ! [D_470] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_470)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_470)
      | ~ m1_pre_topc(D_470,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_2696])).

tff(c_2700,plain,(
    ! [D_470] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_470)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_470)
      | ~ m1_pre_topc(D_470,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_2699])).

tff(c_2758,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2747,c_2700])).

tff(c_2765,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2758])).

tff(c_2993,plain,(
    ! [D_511,A_507,B_508,C_509,E_510] :
      ( v5_pre_topc(k3_tmap_1(A_507,B_508,k1_tsep_1(A_507,C_509,D_511),D_511,E_510),D_511,B_508)
      | ~ v5_pre_topc(E_510,k1_tsep_1(A_507,C_509,D_511),B_508)
      | ~ m1_subset_1(E_510,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_507,C_509,D_511)),u1_struct_0(B_508))))
      | ~ v1_funct_2(E_510,u1_struct_0(k1_tsep_1(A_507,C_509,D_511)),u1_struct_0(B_508))
      | ~ v1_funct_1(E_510)
      | ~ r4_tsep_1(A_507,C_509,D_511)
      | ~ m1_pre_topc(D_511,A_507)
      | v2_struct_0(D_511)
      | ~ m1_pre_topc(C_509,A_507)
      | v2_struct_0(C_509)
      | ~ l1_pre_topc(B_508)
      | ~ v2_pre_topc(B_508)
      | v2_struct_0(B_508)
      | ~ l1_pre_topc(A_507)
      | ~ v2_pre_topc(A_507)
      | v2_struct_0(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2995,plain,(
    ! [B_508,E_510] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_508,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_510),'#skF_5',B_508)
      | ~ v5_pre_topc(E_510,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_508)
      | ~ m1_subset_1(E_510,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_508))))
      | ~ v1_funct_2(E_510,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_508))
      | ~ v1_funct_1(E_510)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_508)
      | ~ v2_pre_topc(B_508)
      | v2_struct_0(B_508)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2993])).

tff(c_2997,plain,(
    ! [B_508,E_510] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_508,'#skF_1','#skF_5',E_510),'#skF_5',B_508)
      | ~ v5_pre_topc(E_510,'#skF_1',B_508)
      | ~ m1_subset_1(E_510,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_508))))
      | ~ v1_funct_2(E_510,u1_struct_0('#skF_1'),u1_struct_0(B_508))
      | ~ v1_funct_1(E_510)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_508)
      | ~ v2_pre_topc(B_508)
      | v2_struct_0(B_508)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_36,c_32,c_34,c_34,c_34,c_2995])).

tff(c_2999,plain,(
    ! [B_512,E_513] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_512,'#skF_1','#skF_5',E_513),'#skF_5',B_512)
      | ~ v5_pre_topc(E_513,'#skF_1',B_512)
      | ~ m1_subset_1(E_513,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_512))))
      | ~ v1_funct_2(E_513,u1_struct_0('#skF_1'),u1_struct_0(B_512))
      | ~ v1_funct_1(E_513)
      | ~ l1_pre_topc(B_512)
      | ~ v2_pre_topc(B_512)
      | v2_struct_0(B_512) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_42,c_38,c_2997])).

tff(c_3001,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'),'#skF_5','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_2999])).

tff(c_3004,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_2688,c_2765,c_3001])).

tff(c_3006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2689,c_3004])).

tff(c_3008,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_3007,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_3030,plain,(
    ! [E_520,D_521,A_523,C_522,B_519] :
      ( k3_tmap_1(A_523,B_519,C_522,D_521,E_520) = k2_partfun1(u1_struct_0(C_522),u1_struct_0(B_519),E_520,u1_struct_0(D_521))
      | ~ m1_pre_topc(D_521,C_522)
      | ~ m1_subset_1(E_520,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_522),u1_struct_0(B_519))))
      | ~ v1_funct_2(E_520,u1_struct_0(C_522),u1_struct_0(B_519))
      | ~ v1_funct_1(E_520)
      | ~ m1_pre_topc(D_521,A_523)
      | ~ m1_pre_topc(C_522,A_523)
      | ~ l1_pre_topc(B_519)
      | ~ v2_pre_topc(B_519)
      | v2_struct_0(B_519)
      | ~ l1_pre_topc(A_523)
      | ~ v2_pre_topc(A_523)
      | v2_struct_0(A_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3032,plain,(
    ! [A_523,D_521] :
      ( k3_tmap_1(A_523,'#skF_2','#skF_1',D_521,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_521))
      | ~ m1_pre_topc(D_521,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_521,A_523)
      | ~ m1_pre_topc('#skF_1',A_523)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_523)
      | ~ v2_pre_topc(A_523)
      | v2_struct_0(A_523) ) ),
    inference(resolution,[status(thm)],[c_44,c_3030])).

tff(c_3035,plain,(
    ! [A_523,D_521] :
      ( k3_tmap_1(A_523,'#skF_2','#skF_1',D_521,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_521))
      | ~ m1_pre_topc(D_521,'#skF_1')
      | ~ m1_pre_topc(D_521,A_523)
      | ~ m1_pre_topc('#skF_1',A_523)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_523)
      | ~ v2_pre_topc(A_523)
      | v2_struct_0(A_523) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_3032])).

tff(c_3037,plain,(
    ! [A_524,D_525] :
      ( k3_tmap_1(A_524,'#skF_2','#skF_1',D_525,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_525))
      | ~ m1_pre_topc(D_525,'#skF_1')
      | ~ m1_pre_topc(D_525,A_524)
      | ~ m1_pre_topc('#skF_1',A_524)
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3035])).

tff(c_3041,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_3037])).

tff(c_3047,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_36,c_3041])).

tff(c_3048,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3047])).

tff(c_3053,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3048])).

tff(c_3056,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3053])).

tff(c_3060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3056])).

tff(c_3062,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_3048])).

tff(c_3043,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_3037])).

tff(c_3051,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_3043])).

tff(c_3052,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3051])).

tff(c_3131,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3062,c_3052])).

tff(c_3014,plain,(
    ! [A_514,B_515,C_516,D_517] :
      ( k2_partfun1(u1_struct_0(A_514),u1_struct_0(B_515),C_516,u1_struct_0(D_517)) = k2_tmap_1(A_514,B_515,C_516,D_517)
      | ~ m1_pre_topc(D_517,A_514)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_514),u1_struct_0(B_515))))
      | ~ v1_funct_2(C_516,u1_struct_0(A_514),u1_struct_0(B_515))
      | ~ v1_funct_1(C_516)
      | ~ l1_pre_topc(B_515)
      | ~ v2_pre_topc(B_515)
      | v2_struct_0(B_515)
      | ~ l1_pre_topc(A_514)
      | ~ v2_pre_topc(A_514)
      | v2_struct_0(A_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3016,plain,(
    ! [D_517] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_517)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_517)
      | ~ m1_pre_topc(D_517,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_3014])).

tff(c_3019,plain,(
    ! [D_517] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_517)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_517)
      | ~ m1_pre_topc(D_517,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_3016])).

tff(c_3020,plain,(
    ! [D_517] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_517)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_517)
      | ~ m1_pre_topc(D_517,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_3019])).

tff(c_3135,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3131,c_3020])).

tff(c_3142,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3135])).

tff(c_3307,plain,(
    ! [C_551,A_549,E_552,B_550,D_553] :
      ( v5_pre_topc(k3_tmap_1(A_549,B_550,k1_tsep_1(A_549,C_551,D_553),C_551,E_552),C_551,B_550)
      | ~ v5_pre_topc(E_552,k1_tsep_1(A_549,C_551,D_553),B_550)
      | ~ m1_subset_1(E_552,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_549,C_551,D_553)),u1_struct_0(B_550))))
      | ~ v1_funct_2(E_552,u1_struct_0(k1_tsep_1(A_549,C_551,D_553)),u1_struct_0(B_550))
      | ~ v1_funct_1(E_552)
      | ~ r4_tsep_1(A_549,C_551,D_553)
      | ~ m1_pre_topc(D_553,A_549)
      | v2_struct_0(D_553)
      | ~ m1_pre_topc(C_551,A_549)
      | v2_struct_0(C_551)
      | ~ l1_pre_topc(B_550)
      | ~ v2_pre_topc(B_550)
      | v2_struct_0(B_550)
      | ~ l1_pre_topc(A_549)
      | ~ v2_pre_topc(A_549)
      | v2_struct_0(A_549) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3309,plain,(
    ! [B_550,E_552] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_550,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_552),'#skF_4',B_550)
      | ~ v5_pre_topc(E_552,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_550)
      | ~ m1_subset_1(E_552,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_550))))
      | ~ v1_funct_2(E_552,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_550))
      | ~ v1_funct_1(E_552)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_550)
      | ~ v2_pre_topc(B_550)
      | v2_struct_0(B_550)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3307])).

tff(c_3311,plain,(
    ! [B_550,E_552] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_550,'#skF_1','#skF_4',E_552),'#skF_4',B_550)
      | ~ v5_pre_topc(E_552,'#skF_1',B_550)
      | ~ m1_subset_1(E_552,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_550))))
      | ~ v1_funct_2(E_552,u1_struct_0('#skF_1'),u1_struct_0(B_550))
      | ~ v1_funct_1(E_552)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_550)
      | ~ v2_pre_topc(B_550)
      | v2_struct_0(B_550)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_36,c_32,c_34,c_34,c_34,c_3309])).

tff(c_3313,plain,(
    ! [B_554,E_555] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_554,'#skF_1','#skF_4',E_555),'#skF_4',B_554)
      | ~ v5_pre_topc(E_555,'#skF_1',B_554)
      | ~ m1_subset_1(E_555,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_554))))
      | ~ v1_funct_2(E_555,u1_struct_0('#skF_1'),u1_struct_0(B_554))
      | ~ v1_funct_1(E_555)
      | ~ l1_pre_topc(B_554)
      | ~ v2_pre_topc(B_554)
      | v2_struct_0(B_554) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_42,c_38,c_3311])).

tff(c_3315,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_3313])).

tff(c_3318,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_3007,c_3142,c_3315])).

tff(c_3320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3008,c_3318])).

tff(c_3322,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_3321,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_3345,plain,(
    ! [D_563,C_564,B_561,A_565,E_562] :
      ( k3_tmap_1(A_565,B_561,C_564,D_563,E_562) = k2_partfun1(u1_struct_0(C_564),u1_struct_0(B_561),E_562,u1_struct_0(D_563))
      | ~ m1_pre_topc(D_563,C_564)
      | ~ m1_subset_1(E_562,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_564),u1_struct_0(B_561))))
      | ~ v1_funct_2(E_562,u1_struct_0(C_564),u1_struct_0(B_561))
      | ~ v1_funct_1(E_562)
      | ~ m1_pre_topc(D_563,A_565)
      | ~ m1_pre_topc(C_564,A_565)
      | ~ l1_pre_topc(B_561)
      | ~ v2_pre_topc(B_561)
      | v2_struct_0(B_561)
      | ~ l1_pre_topc(A_565)
      | ~ v2_pre_topc(A_565)
      | v2_struct_0(A_565) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3347,plain,(
    ! [A_565,D_563] :
      ( k3_tmap_1(A_565,'#skF_2','#skF_1',D_563,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_563))
      | ~ m1_pre_topc(D_563,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_563,A_565)
      | ~ m1_pre_topc('#skF_1',A_565)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_565)
      | ~ v2_pre_topc(A_565)
      | v2_struct_0(A_565) ) ),
    inference(resolution,[status(thm)],[c_44,c_3345])).

tff(c_3350,plain,(
    ! [A_565,D_563] :
      ( k3_tmap_1(A_565,'#skF_2','#skF_1',D_563,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_563))
      | ~ m1_pre_topc(D_563,'#skF_1')
      | ~ m1_pre_topc(D_563,A_565)
      | ~ m1_pre_topc('#skF_1',A_565)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_565)
      | ~ v2_pre_topc(A_565)
      | v2_struct_0(A_565) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_3347])).

tff(c_3352,plain,(
    ! [A_566,D_567] :
      ( k3_tmap_1(A_566,'#skF_2','#skF_1',D_567,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_567))
      | ~ m1_pre_topc(D_567,'#skF_1')
      | ~ m1_pre_topc(D_567,A_566)
      | ~ m1_pre_topc('#skF_1',A_566)
      | ~ l1_pre_topc(A_566)
      | ~ v2_pre_topc(A_566)
      | v2_struct_0(A_566) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3350])).

tff(c_3356,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_3352])).

tff(c_3362,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_36,c_3356])).

tff(c_3363,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3362])).

tff(c_3368,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3363])).

tff(c_3377,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3368])).

tff(c_3381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3377])).

tff(c_3382,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3363])).

tff(c_3329,plain,(
    ! [A_556,B_557,C_558,D_559] :
      ( k2_partfun1(u1_struct_0(A_556),u1_struct_0(B_557),C_558,u1_struct_0(D_559)) = k2_tmap_1(A_556,B_557,C_558,D_559)
      | ~ m1_pre_topc(D_559,A_556)
      | ~ m1_subset_1(C_558,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_556),u1_struct_0(B_557))))
      | ~ v1_funct_2(C_558,u1_struct_0(A_556),u1_struct_0(B_557))
      | ~ v1_funct_1(C_558)
      | ~ l1_pre_topc(B_557)
      | ~ v2_pre_topc(B_557)
      | v2_struct_0(B_557)
      | ~ l1_pre_topc(A_556)
      | ~ v2_pre_topc(A_556)
      | v2_struct_0(A_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3331,plain,(
    ! [D_559] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_559)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_559)
      | ~ m1_pre_topc(D_559,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_3329])).

tff(c_3334,plain,(
    ! [D_559] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_559)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_559)
      | ~ m1_pre_topc(D_559,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_3331])).

tff(c_3335,plain,(
    ! [D_559] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_559)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_559)
      | ~ m1_pre_topc(D_559,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_3334])).

tff(c_3393,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3382,c_3335])).

tff(c_3400,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3393])).

tff(c_3574,plain,(
    ! [C_583,A_581,D_585,B_582,E_584] :
      ( v1_funct_1(k3_tmap_1(A_581,B_582,k1_tsep_1(A_581,C_583,D_585),D_585,E_584))
      | ~ v5_pre_topc(E_584,k1_tsep_1(A_581,C_583,D_585),B_582)
      | ~ m1_subset_1(E_584,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_581,C_583,D_585)),u1_struct_0(B_582))))
      | ~ v1_funct_2(E_584,u1_struct_0(k1_tsep_1(A_581,C_583,D_585)),u1_struct_0(B_582))
      | ~ v1_funct_1(E_584)
      | ~ r4_tsep_1(A_581,C_583,D_585)
      | ~ m1_pre_topc(D_585,A_581)
      | v2_struct_0(D_585)
      | ~ m1_pre_topc(C_583,A_581)
      | v2_struct_0(C_583)
      | ~ l1_pre_topc(B_582)
      | ~ v2_pre_topc(B_582)
      | v2_struct_0(B_582)
      | ~ l1_pre_topc(A_581)
      | ~ v2_pre_topc(A_581)
      | v2_struct_0(A_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3576,plain,(
    ! [B_582,E_584] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_582,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_584))
      | ~ v5_pre_topc(E_584,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_582)
      | ~ m1_subset_1(E_584,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_582))))
      | ~ v1_funct_2(E_584,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_582))
      | ~ v1_funct_1(E_584)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_582)
      | ~ v2_pre_topc(B_582)
      | v2_struct_0(B_582)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3574])).

tff(c_3578,plain,(
    ! [B_582,E_584] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_582,'#skF_1','#skF_5',E_584))
      | ~ v5_pre_topc(E_584,'#skF_1',B_582)
      | ~ m1_subset_1(E_584,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_582))))
      | ~ v1_funct_2(E_584,u1_struct_0('#skF_1'),u1_struct_0(B_582))
      | ~ v1_funct_1(E_584)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_582)
      | ~ v2_pre_topc(B_582)
      | v2_struct_0(B_582)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_36,c_32,c_34,c_34,c_34,c_3576])).

tff(c_3607,plain,(
    ! [B_587,E_588] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_587,'#skF_1','#skF_5',E_588))
      | ~ v5_pre_topc(E_588,'#skF_1',B_587)
      | ~ m1_subset_1(E_588,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_587))))
      | ~ v1_funct_2(E_588,u1_struct_0('#skF_1'),u1_struct_0(B_587))
      | ~ v1_funct_1(E_588)
      | ~ l1_pre_topc(B_587)
      | ~ v2_pre_topc(B_587)
      | v2_struct_0(B_587) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_42,c_38,c_3578])).

tff(c_3610,plain,
    ( v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_3607])).

tff(c_3613,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_3321,c_3400,c_3610])).

tff(c_3615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3322,c_3613])).

tff(c_3617,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_3616,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_3641,plain,(
    ! [E_595,A_598,B_594,D_596,C_597] :
      ( k3_tmap_1(A_598,B_594,C_597,D_596,E_595) = k2_partfun1(u1_struct_0(C_597),u1_struct_0(B_594),E_595,u1_struct_0(D_596))
      | ~ m1_pre_topc(D_596,C_597)
      | ~ m1_subset_1(E_595,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_597),u1_struct_0(B_594))))
      | ~ v1_funct_2(E_595,u1_struct_0(C_597),u1_struct_0(B_594))
      | ~ v1_funct_1(E_595)
      | ~ m1_pre_topc(D_596,A_598)
      | ~ m1_pre_topc(C_597,A_598)
      | ~ l1_pre_topc(B_594)
      | ~ v2_pre_topc(B_594)
      | v2_struct_0(B_594)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3643,plain,(
    ! [A_598,D_596] :
      ( k3_tmap_1(A_598,'#skF_2','#skF_1',D_596,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_596))
      | ~ m1_pre_topc(D_596,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_596,A_598)
      | ~ m1_pre_topc('#skF_1',A_598)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(resolution,[status(thm)],[c_44,c_3641])).

tff(c_3646,plain,(
    ! [A_598,D_596] :
      ( k3_tmap_1(A_598,'#skF_2','#skF_1',D_596,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_596))
      | ~ m1_pre_topc(D_596,'#skF_1')
      | ~ m1_pre_topc(D_596,A_598)
      | ~ m1_pre_topc('#skF_1',A_598)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_3643])).

tff(c_3654,plain,(
    ! [A_604,D_605] :
      ( k3_tmap_1(A_604,'#skF_2','#skF_1',D_605,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_605))
      | ~ m1_pre_topc(D_605,'#skF_1')
      | ~ m1_pre_topc(D_605,A_604)
      | ~ m1_pre_topc('#skF_1',A_604)
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3646])).

tff(c_3658,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_3654])).

tff(c_3664,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_36,c_3658])).

tff(c_3665,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3664])).

tff(c_3670,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3665])).

tff(c_3673,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3670])).

tff(c_3677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3673])).

tff(c_3679,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_3665])).

tff(c_3660,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_3654])).

tff(c_3668,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_3660])).

tff(c_3669,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3668])).

tff(c_3680,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3669])).

tff(c_3688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3679,c_3680])).

tff(c_3689,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3669])).

tff(c_3625,plain,(
    ! [A_589,B_590,C_591,D_592] :
      ( k2_partfun1(u1_struct_0(A_589),u1_struct_0(B_590),C_591,u1_struct_0(D_592)) = k2_tmap_1(A_589,B_590,C_591,D_592)
      | ~ m1_pre_topc(D_592,A_589)
      | ~ m1_subset_1(C_591,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_589),u1_struct_0(B_590))))
      | ~ v1_funct_2(C_591,u1_struct_0(A_589),u1_struct_0(B_590))
      | ~ v1_funct_1(C_591)
      | ~ l1_pre_topc(B_590)
      | ~ v2_pre_topc(B_590)
      | v2_struct_0(B_590)
      | ~ l1_pre_topc(A_589)
      | ~ v2_pre_topc(A_589)
      | v2_struct_0(A_589) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3627,plain,(
    ! [D_592] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_592)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_592)
      | ~ m1_pre_topc(D_592,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_3625])).

tff(c_3630,plain,(
    ! [D_592] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_592)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_592)
      | ~ m1_pre_topc(D_592,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_3627])).

tff(c_3631,plain,(
    ! [D_592] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_592)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_592)
      | ~ m1_pre_topc(D_592,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_3630])).

tff(c_3701,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3689,c_3631])).

tff(c_3708,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3701])).

tff(c_3712,plain,(
    ! [A_606,D_610,E_609,B_607,C_608] :
      ( v1_funct_1(k3_tmap_1(A_606,B_607,k1_tsep_1(A_606,C_608,D_610),C_608,E_609))
      | ~ v5_pre_topc(E_609,k1_tsep_1(A_606,C_608,D_610),B_607)
      | ~ m1_subset_1(E_609,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_606,C_608,D_610)),u1_struct_0(B_607))))
      | ~ v1_funct_2(E_609,u1_struct_0(k1_tsep_1(A_606,C_608,D_610)),u1_struct_0(B_607))
      | ~ v1_funct_1(E_609)
      | ~ r4_tsep_1(A_606,C_608,D_610)
      | ~ m1_pre_topc(D_610,A_606)
      | v2_struct_0(D_610)
      | ~ m1_pre_topc(C_608,A_606)
      | v2_struct_0(C_608)
      | ~ l1_pre_topc(B_607)
      | ~ v2_pre_topc(B_607)
      | v2_struct_0(B_607)
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606)
      | v2_struct_0(A_606) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3714,plain,(
    ! [B_607,E_609] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_607,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_609))
      | ~ v5_pre_topc(E_609,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_607)
      | ~ m1_subset_1(E_609,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_607))))
      | ~ v1_funct_2(E_609,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_607))
      | ~ v1_funct_1(E_609)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_607)
      | ~ v2_pre_topc(B_607)
      | v2_struct_0(B_607)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3712])).

tff(c_3716,plain,(
    ! [B_607,E_609] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_607,'#skF_1','#skF_4',E_609))
      | ~ v5_pre_topc(E_609,'#skF_1',B_607)
      | ~ m1_subset_1(E_609,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_607))))
      | ~ v1_funct_2(E_609,u1_struct_0('#skF_1'),u1_struct_0(B_607))
      | ~ v1_funct_1(E_609)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_607)
      | ~ v2_pre_topc(B_607)
      | v2_struct_0(B_607)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_36,c_32,c_34,c_34,c_34,c_3714])).

tff(c_3919,plain,(
    ! [B_625,E_626] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_625,'#skF_1','#skF_4',E_626))
      | ~ v5_pre_topc(E_626,'#skF_1',B_625)
      | ~ m1_subset_1(E_626,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_625))))
      | ~ v1_funct_2(E_626,u1_struct_0('#skF_1'),u1_struct_0(B_625))
      | ~ v1_funct_1(E_626)
      | ~ l1_pre_topc(B_625)
      | ~ v2_pre_topc(B_625)
      | v2_struct_0(B_625) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_42,c_38,c_3716])).

tff(c_3922,plain,
    ( v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_3919])).

tff(c_3925,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_3616,c_3708,c_3922])).

tff(c_3927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3617,c_3925])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.30/2.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.51  
% 7.69/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.51  %$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.69/2.51  
% 7.69/2.51  %Foreground sorts:
% 7.69/2.51  
% 7.69/2.51  
% 7.69/2.51  %Background operators:
% 7.69/2.51  
% 7.69/2.51  
% 7.69/2.51  %Foreground operators:
% 7.69/2.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.69/2.51  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 7.69/2.51  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.69/2.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.69/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.69/2.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.69/2.51  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 7.69/2.51  tff('#skF_5', type, '#skF_5': $i).
% 7.69/2.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.69/2.51  tff('#skF_2', type, '#skF_2': $i).
% 7.69/2.51  tff('#skF_3', type, '#skF_3': $i).
% 7.69/2.51  tff('#skF_1', type, '#skF_1': $i).
% 7.69/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.69/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.69/2.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.69/2.51  tff('#skF_4', type, '#skF_4': $i).
% 7.69/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.69/2.51  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.69/2.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.69/2.51  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.69/2.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.69/2.51  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.69/2.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.69/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.69/2.51  
% 7.69/2.56  tff(f_211, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (((A = k1_tsep_1(A, D, E)) & r4_tsep_1(A, D, E)) => ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, C, E))) & v1_funct_2(k2_tmap_1(A, B, C, E), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, E), E, B)) & m1_subset_1(k2_tmap_1(A, B, C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_tmap_1)).
% 7.69/2.56  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.69/2.56  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 7.69/2.56  tff(f_52, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.69/2.56  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_tmap_1)).
% 7.69/2.56  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_146, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_186, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_146])).
% 7.69/2.56  tff(c_136, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_190, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_136])).
% 7.69/2.56  tff(c_126, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_188, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_126])).
% 7.69/2.56  tff(c_116, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_193, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_116])).
% 7.69/2.56  tff(c_106, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_187, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_106])).
% 7.69/2.56  tff(c_96, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_191, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_96])).
% 7.69/2.56  tff(c_86, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_189, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_86])).
% 7.69/2.56  tff(c_76, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_192, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_76])).
% 7.69/2.56  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_46, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_62, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_160, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 7.69/2.56  tff(c_170, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_160])).
% 7.69/2.56  tff(c_180, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_170])).
% 7.69/2.56  tff(c_833, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_190, c_188, c_193, c_187, c_191, c_189, c_192, c_180])).
% 7.69/2.56  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_30, plain, (![A_78]: (m1_pre_topc(A_78, A_78) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.69/2.56  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_36, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_223, plain, (![B_111, C_114, A_115, D_113, E_112]: (k3_tmap_1(A_115, B_111, C_114, D_113, E_112)=k2_partfun1(u1_struct_0(C_114), u1_struct_0(B_111), E_112, u1_struct_0(D_113)) | ~m1_pre_topc(D_113, C_114) | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_114), u1_struct_0(B_111)))) | ~v1_funct_2(E_112, u1_struct_0(C_114), u1_struct_0(B_111)) | ~v1_funct_1(E_112) | ~m1_pre_topc(D_113, A_115) | ~m1_pre_topc(C_114, A_115) | ~l1_pre_topc(B_111) | ~v2_pre_topc(B_111) | v2_struct_0(B_111) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.69/2.56  tff(c_229, plain, (![A_115, D_113]: (k3_tmap_1(A_115, '#skF_2', '#skF_1', D_113, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_113)) | ~m1_pre_topc(D_113, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_113, A_115) | ~m1_pre_topc('#skF_1', A_115) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(resolution, [status(thm)], [c_44, c_223])).
% 7.69/2.56  tff(c_240, plain, (![A_115, D_113]: (k3_tmap_1(A_115, '#skF_2', '#skF_1', D_113, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_113)) | ~m1_pre_topc(D_113, '#skF_1') | ~m1_pre_topc(D_113, A_115) | ~m1_pre_topc('#skF_1', A_115) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_229])).
% 7.69/2.56  tff(c_243, plain, (![A_116, D_117]: (k3_tmap_1(A_116, '#skF_2', '#skF_1', D_117, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_117)) | ~m1_pre_topc(D_117, '#skF_1') | ~m1_pre_topc(D_117, A_116) | ~m1_pre_topc('#skF_1', A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(negUnitSimplification, [status(thm)], [c_54, c_240])).
% 7.69/2.56  tff(c_247, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_243])).
% 7.69/2.56  tff(c_253, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_36, c_247])).
% 7.69/2.56  tff(c_254, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_253])).
% 7.69/2.56  tff(c_259, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_254])).
% 7.69/2.56  tff(c_262, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_259])).
% 7.69/2.56  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_262])).
% 7.69/2.56  tff(c_268, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_254])).
% 7.69/2.56  tff(c_249, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_243])).
% 7.69/2.56  tff(c_257, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_249])).
% 7.69/2.56  tff(c_258, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_257])).
% 7.69/2.56  tff(c_332, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_258])).
% 7.69/2.56  tff(c_194, plain, (![A_106, B_107, C_108, D_109]: (k2_partfun1(u1_struct_0(A_106), u1_struct_0(B_107), C_108, u1_struct_0(D_109))=k2_tmap_1(A_106, B_107, C_108, D_109) | ~m1_pre_topc(D_109, A_106) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_106), u1_struct_0(B_107)))) | ~v1_funct_2(C_108, u1_struct_0(A_106), u1_struct_0(B_107)) | ~v1_funct_1(C_108) | ~l1_pre_topc(B_107) | ~v2_pre_topc(B_107) | v2_struct_0(B_107) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.69/2.56  tff(c_200, plain, (![D_109]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_109))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_109) | ~m1_pre_topc(D_109, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_194])).
% 7.69/2.56  tff(c_211, plain, (![D_109]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_109))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_109) | ~m1_pre_topc(D_109, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_200])).
% 7.69/2.56  tff(c_212, plain, (![D_109]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_109))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_109) | ~m1_pre_topc(D_109, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_211])).
% 7.69/2.56  tff(c_336, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_332, c_212])).
% 7.69/2.56  tff(c_343, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_336])).
% 7.69/2.56  tff(c_267, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_254])).
% 7.69/2.56  tff(c_278, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_267, c_212])).
% 7.69/2.56  tff(c_285, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_278])).
% 7.69/2.56  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_38, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_32, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_34, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_211])).
% 7.69/2.56  tff(c_874, plain, (![E_205, A_202, C_204, B_203, D_206]: (v5_pre_topc(E_205, k1_tsep_1(A_202, C_204, D_206), B_203) | ~m1_subset_1(k3_tmap_1(A_202, B_203, k1_tsep_1(A_202, C_204, D_206), D_206, E_205), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_206), u1_struct_0(B_203)))) | ~v5_pre_topc(k3_tmap_1(A_202, B_203, k1_tsep_1(A_202, C_204, D_206), D_206, E_205), D_206, B_203) | ~v1_funct_2(k3_tmap_1(A_202, B_203, k1_tsep_1(A_202, C_204, D_206), D_206, E_205), u1_struct_0(D_206), u1_struct_0(B_203)) | ~v1_funct_1(k3_tmap_1(A_202, B_203, k1_tsep_1(A_202, C_204, D_206), D_206, E_205)) | ~m1_subset_1(k3_tmap_1(A_202, B_203, k1_tsep_1(A_202, C_204, D_206), C_204, E_205), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_204), u1_struct_0(B_203)))) | ~v5_pre_topc(k3_tmap_1(A_202, B_203, k1_tsep_1(A_202, C_204, D_206), C_204, E_205), C_204, B_203) | ~v1_funct_2(k3_tmap_1(A_202, B_203, k1_tsep_1(A_202, C_204, D_206), C_204, E_205), u1_struct_0(C_204), u1_struct_0(B_203)) | ~v1_funct_1(k3_tmap_1(A_202, B_203, k1_tsep_1(A_202, C_204, D_206), C_204, E_205)) | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_202, C_204, D_206)), u1_struct_0(B_203)))) | ~v1_funct_2(E_205, u1_struct_0(k1_tsep_1(A_202, C_204, D_206)), u1_struct_0(B_203)) | ~v1_funct_1(E_205) | ~r4_tsep_1(A_202, C_204, D_206) | ~m1_pre_topc(D_206, A_202) | v2_struct_0(D_206) | ~m1_pre_topc(C_204, A_202) | v2_struct_0(C_204) | ~l1_pre_topc(B_203) | ~v2_pre_topc(B_203) | v2_struct_0(B_203) | ~l1_pre_topc(A_202) | ~v2_pre_topc(A_202) | v2_struct_0(A_202))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.69/2.56  tff(c_881, plain, (![E_205, B_203]: (v5_pre_topc(E_205, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_203) | ~m1_subset_1(k3_tmap_1('#skF_1', B_203, '#skF_1', '#skF_5', E_205), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_203)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_203, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_205), '#skF_5', B_203) | ~v1_funct_2(k3_tmap_1('#skF_1', B_203, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_205), u1_struct_0('#skF_5'), u1_struct_0(B_203)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_203, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_205)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_203, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_205), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_203)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_203, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_205), '#skF_4', B_203) | ~v1_funct_2(k3_tmap_1('#skF_1', B_203, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_205), u1_struct_0('#skF_4'), u1_struct_0(B_203)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_203, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_205)) | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_203)))) | ~v1_funct_2(E_205, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_203)) | ~v1_funct_1(E_205) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_203) | ~v2_pre_topc(B_203) | v2_struct_0(B_203) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_874])).
% 7.69/2.56  tff(c_885, plain, (![E_205, B_203]: (v5_pre_topc(E_205, '#skF_1', B_203) | ~m1_subset_1(k3_tmap_1('#skF_1', B_203, '#skF_1', '#skF_5', E_205), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_203)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_203, '#skF_1', '#skF_5', E_205), '#skF_5', B_203) | ~v1_funct_2(k3_tmap_1('#skF_1', B_203, '#skF_1', '#skF_5', E_205), u1_struct_0('#skF_5'), u1_struct_0(B_203)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_203, '#skF_1', '#skF_5', E_205)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_203, '#skF_1', '#skF_4', E_205), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_203)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_203, '#skF_1', '#skF_4', E_205), '#skF_4', B_203) | ~v1_funct_2(k3_tmap_1('#skF_1', B_203, '#skF_1', '#skF_4', E_205), u1_struct_0('#skF_4'), u1_struct_0(B_203)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_203, '#skF_1', '#skF_4', E_205)) | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_203)))) | ~v1_funct_2(E_205, u1_struct_0('#skF_1'), u1_struct_0(B_203)) | ~v1_funct_1(E_205) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_203) | ~v2_pre_topc(B_203) | v2_struct_0(B_203) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_36, c_32, c_34, c_34, c_34, c_34, c_34, c_34, c_34, c_34, c_34, c_34, c_881])).
% 7.69/2.56  tff(c_889, plain, (![E_215, B_216]: (v5_pre_topc(E_215, '#skF_1', B_216) | ~m1_subset_1(k3_tmap_1('#skF_1', B_216, '#skF_1', '#skF_5', E_215), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_216)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_216, '#skF_1', '#skF_5', E_215), '#skF_5', B_216) | ~v1_funct_2(k3_tmap_1('#skF_1', B_216, '#skF_1', '#skF_5', E_215), u1_struct_0('#skF_5'), u1_struct_0(B_216)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_216, '#skF_1', '#skF_5', E_215)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_216, '#skF_1', '#skF_4', E_215), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_216)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_216, '#skF_1', '#skF_4', E_215), '#skF_4', B_216) | ~v1_funct_2(k3_tmap_1('#skF_1', B_216, '#skF_1', '#skF_4', E_215), u1_struct_0('#skF_4'), u1_struct_0(B_216)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_216, '#skF_1', '#skF_4', E_215)) | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_216)))) | ~v1_funct_2(E_215, u1_struct_0('#skF_1'), u1_struct_0(B_216)) | ~v1_funct_1(E_215) | ~l1_pre_topc(B_216) | ~v2_pre_topc(B_216) | v2_struct_0(B_216))), inference(negUnitSimplification, [status(thm)], [c_60, c_42, c_38, c_885])).
% 7.69/2.56  tff(c_895, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), '#skF_5', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_285, c_889])).
% 7.69/2.56  tff(c_898, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_186, c_343, c_190, c_343, c_188, c_343, c_193, c_343, c_187, c_285, c_191, c_285, c_189, c_285, c_192, c_895])).
% 7.69/2.56  tff(c_900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_833, c_898])).
% 7.69/2.56  tff(c_902, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_116])).
% 7.69/2.56  tff(c_901, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_116])).
% 7.69/2.56  tff(c_926, plain, (![B_222, C_225, E_223, D_224, A_226]: (k3_tmap_1(A_226, B_222, C_225, D_224, E_223)=k2_partfun1(u1_struct_0(C_225), u1_struct_0(B_222), E_223, u1_struct_0(D_224)) | ~m1_pre_topc(D_224, C_225) | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_225), u1_struct_0(B_222)))) | ~v1_funct_2(E_223, u1_struct_0(C_225), u1_struct_0(B_222)) | ~v1_funct_1(E_223) | ~m1_pre_topc(D_224, A_226) | ~m1_pre_topc(C_225, A_226) | ~l1_pre_topc(B_222) | ~v2_pre_topc(B_222) | v2_struct_0(B_222) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.69/2.56  tff(c_930, plain, (![A_226, D_224]: (k3_tmap_1(A_226, '#skF_2', '#skF_1', D_224, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_224)) | ~m1_pre_topc(D_224, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_224, A_226) | ~m1_pre_topc('#skF_1', A_226) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(resolution, [status(thm)], [c_44, c_926])).
% 7.69/2.56  tff(c_937, plain, (![A_226, D_224]: (k3_tmap_1(A_226, '#skF_2', '#skF_1', D_224, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_224)) | ~m1_pre_topc(D_224, '#skF_1') | ~m1_pre_topc(D_224, A_226) | ~m1_pre_topc('#skF_1', A_226) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_930])).
% 7.69/2.56  tff(c_939, plain, (![A_227, D_228]: (k3_tmap_1(A_227, '#skF_2', '#skF_1', D_228, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_228)) | ~m1_pre_topc(D_228, '#skF_1') | ~m1_pre_topc(D_228, A_227) | ~m1_pre_topc('#skF_1', A_227) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(negUnitSimplification, [status(thm)], [c_54, c_937])).
% 7.69/2.56  tff(c_943, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_939])).
% 7.69/2.56  tff(c_949, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_36, c_943])).
% 7.69/2.56  tff(c_950, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_949])).
% 7.69/2.56  tff(c_955, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_950])).
% 7.69/2.56  tff(c_959, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_955])).
% 7.69/2.56  tff(c_963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_959])).
% 7.69/2.56  tff(c_965, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_950])).
% 7.69/2.56  tff(c_945, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_939])).
% 7.69/2.56  tff(c_953, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_945])).
% 7.69/2.56  tff(c_954, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_953])).
% 7.69/2.56  tff(c_1034, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_965, c_954])).
% 7.69/2.56  tff(c_903, plain, (![A_217, B_218, C_219, D_220]: (k2_partfun1(u1_struct_0(A_217), u1_struct_0(B_218), C_219, u1_struct_0(D_220))=k2_tmap_1(A_217, B_218, C_219, D_220) | ~m1_pre_topc(D_220, A_217) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_217), u1_struct_0(B_218)))) | ~v1_funct_2(C_219, u1_struct_0(A_217), u1_struct_0(B_218)) | ~v1_funct_1(C_219) | ~l1_pre_topc(B_218) | ~v2_pre_topc(B_218) | v2_struct_0(B_218) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.69/2.56  tff(c_907, plain, (![D_220]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_220))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_220) | ~m1_pre_topc(D_220, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_903])).
% 7.69/2.56  tff(c_914, plain, (![D_220]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_220))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_220) | ~m1_pre_topc(D_220, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_907])).
% 7.69/2.56  tff(c_915, plain, (![D_220]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_220))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_220) | ~m1_pre_topc(D_220, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_914])).
% 7.69/2.56  tff(c_1038, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1034, c_915])).
% 7.69/2.56  tff(c_1045, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1038])).
% 7.69/2.56  tff(c_1295, plain, (![C_278, D_280, A_276, B_277, E_279]: (m1_subset_1(k3_tmap_1(A_276, B_277, k1_tsep_1(A_276, C_278, D_280), C_278, E_279), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_278), u1_struct_0(B_277)))) | ~v5_pre_topc(E_279, k1_tsep_1(A_276, C_278, D_280), B_277) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_276, C_278, D_280)), u1_struct_0(B_277)))) | ~v1_funct_2(E_279, u1_struct_0(k1_tsep_1(A_276, C_278, D_280)), u1_struct_0(B_277)) | ~v1_funct_1(E_279) | ~r4_tsep_1(A_276, C_278, D_280) | ~m1_pre_topc(D_280, A_276) | v2_struct_0(D_280) | ~m1_pre_topc(C_278, A_276) | v2_struct_0(C_278) | ~l1_pre_topc(B_277) | ~v2_pre_topc(B_277) | v2_struct_0(B_277) | ~l1_pre_topc(A_276) | ~v2_pre_topc(A_276) | v2_struct_0(A_276))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.69/2.56  tff(c_1337, plain, (![B_277, E_279]: (m1_subset_1(k3_tmap_1('#skF_1', B_277, '#skF_1', '#skF_4', E_279), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_277)))) | ~v5_pre_topc(E_279, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_277) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_277)))) | ~v1_funct_2(E_279, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_277)) | ~v1_funct_1(E_279) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_277) | ~v2_pre_topc(B_277) | v2_struct_0(B_277) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1295])).
% 7.69/2.56  tff(c_1362, plain, (![B_277, E_279]: (m1_subset_1(k3_tmap_1('#skF_1', B_277, '#skF_1', '#skF_4', E_279), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_277)))) | ~v5_pre_topc(E_279, '#skF_1', B_277) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_277)))) | ~v1_funct_2(E_279, u1_struct_0('#skF_1'), u1_struct_0(B_277)) | ~v1_funct_1(E_279) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_277) | ~v2_pre_topc(B_277) | v2_struct_0(B_277) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_36, c_32, c_34, c_34, c_34, c_1337])).
% 7.69/2.56  tff(c_1377, plain, (![B_283, E_284]: (m1_subset_1(k3_tmap_1('#skF_1', B_283, '#skF_1', '#skF_4', E_284), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_283)))) | ~v5_pre_topc(E_284, '#skF_1', B_283) | ~m1_subset_1(E_284, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_283)))) | ~v1_funct_2(E_284, u1_struct_0('#skF_1'), u1_struct_0(B_283)) | ~v1_funct_1(E_284) | ~l1_pre_topc(B_283) | ~v2_pre_topc(B_283) | v2_struct_0(B_283))), inference(negUnitSimplification, [status(thm)], [c_60, c_42, c_38, c_1362])).
% 7.69/2.56  tff(c_1384, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1045, c_1377])).
% 7.69/2.56  tff(c_1389, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_901, c_1384])).
% 7.69/2.56  tff(c_1391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_902, c_1389])).
% 7.69/2.56  tff(c_1393, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_76])).
% 7.69/2.56  tff(c_1392, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_76])).
% 7.69/2.56  tff(c_1411, plain, (![C_293, A_294, B_290, E_291, D_292]: (k3_tmap_1(A_294, B_290, C_293, D_292, E_291)=k2_partfun1(u1_struct_0(C_293), u1_struct_0(B_290), E_291, u1_struct_0(D_292)) | ~m1_pre_topc(D_292, C_293) | ~m1_subset_1(E_291, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_293), u1_struct_0(B_290)))) | ~v1_funct_2(E_291, u1_struct_0(C_293), u1_struct_0(B_290)) | ~v1_funct_1(E_291) | ~m1_pre_topc(D_292, A_294) | ~m1_pre_topc(C_293, A_294) | ~l1_pre_topc(B_290) | ~v2_pre_topc(B_290) | v2_struct_0(B_290) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.69/2.56  tff(c_1413, plain, (![A_294, D_292]: (k3_tmap_1(A_294, '#skF_2', '#skF_1', D_292, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_292)) | ~m1_pre_topc(D_292, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_292, A_294) | ~m1_pre_topc('#skF_1', A_294) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(resolution, [status(thm)], [c_44, c_1411])).
% 7.69/2.56  tff(c_1416, plain, (![A_294, D_292]: (k3_tmap_1(A_294, '#skF_2', '#skF_1', D_292, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_292)) | ~m1_pre_topc(D_292, '#skF_1') | ~m1_pre_topc(D_292, A_294) | ~m1_pre_topc('#skF_1', A_294) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_1413])).
% 7.69/2.56  tff(c_1418, plain, (![A_295, D_296]: (k3_tmap_1(A_295, '#skF_2', '#skF_1', D_296, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_296)) | ~m1_pre_topc(D_296, '#skF_1') | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc('#skF_1', A_295) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(negUnitSimplification, [status(thm)], [c_54, c_1416])).
% 7.69/2.56  tff(c_1422, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1418])).
% 7.69/2.56  tff(c_1428, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_36, c_1422])).
% 7.69/2.56  tff(c_1429, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_1428])).
% 7.69/2.56  tff(c_1440, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_1429])).
% 7.69/2.56  tff(c_1443, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1440])).
% 7.69/2.56  tff(c_1447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1443])).
% 7.69/2.56  tff(c_1448, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_1429])).
% 7.69/2.56  tff(c_1395, plain, (![A_285, B_286, C_287, D_288]: (k2_partfun1(u1_struct_0(A_285), u1_struct_0(B_286), C_287, u1_struct_0(D_288))=k2_tmap_1(A_285, B_286, C_287, D_288) | ~m1_pre_topc(D_288, A_285) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_285), u1_struct_0(B_286)))) | ~v1_funct_2(C_287, u1_struct_0(A_285), u1_struct_0(B_286)) | ~v1_funct_1(C_287) | ~l1_pre_topc(B_286) | ~v2_pre_topc(B_286) | v2_struct_0(B_286) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.69/2.56  tff(c_1397, plain, (![D_288]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_288))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_288) | ~m1_pre_topc(D_288, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_1395])).
% 7.69/2.56  tff(c_1400, plain, (![D_288]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_288))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_288) | ~m1_pre_topc(D_288, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_1397])).
% 7.69/2.56  tff(c_1401, plain, (![D_288]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_288))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_288) | ~m1_pre_topc(D_288, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_1400])).
% 7.69/2.56  tff(c_1495, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1448, c_1401])).
% 7.69/2.56  tff(c_1502, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1495])).
% 7.69/2.56  tff(c_1807, plain, (![D_350, A_346, B_347, E_349, C_348]: (m1_subset_1(k3_tmap_1(A_346, B_347, k1_tsep_1(A_346, C_348, D_350), D_350, E_349), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_350), u1_struct_0(B_347)))) | ~v5_pre_topc(E_349, k1_tsep_1(A_346, C_348, D_350), B_347) | ~m1_subset_1(E_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_346, C_348, D_350)), u1_struct_0(B_347)))) | ~v1_funct_2(E_349, u1_struct_0(k1_tsep_1(A_346, C_348, D_350)), u1_struct_0(B_347)) | ~v1_funct_1(E_349) | ~r4_tsep_1(A_346, C_348, D_350) | ~m1_pre_topc(D_350, A_346) | v2_struct_0(D_350) | ~m1_pre_topc(C_348, A_346) | v2_struct_0(C_348) | ~l1_pre_topc(B_347) | ~v2_pre_topc(B_347) | v2_struct_0(B_347) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.69/2.56  tff(c_1852, plain, (![B_347, E_349]: (m1_subset_1(k3_tmap_1('#skF_1', B_347, '#skF_1', '#skF_5', E_349), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_347)))) | ~v5_pre_topc(E_349, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_347) | ~m1_subset_1(E_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_347)))) | ~v1_funct_2(E_349, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_347)) | ~v1_funct_1(E_349) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_347) | ~v2_pre_topc(B_347) | v2_struct_0(B_347) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1807])).
% 7.69/2.56  tff(c_1880, plain, (![B_347, E_349]: (m1_subset_1(k3_tmap_1('#skF_1', B_347, '#skF_1', '#skF_5', E_349), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_347)))) | ~v5_pre_topc(E_349, '#skF_1', B_347) | ~m1_subset_1(E_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_347)))) | ~v1_funct_2(E_349, u1_struct_0('#skF_1'), u1_struct_0(B_347)) | ~v1_funct_1(E_349) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_347) | ~v2_pre_topc(B_347) | v2_struct_0(B_347) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_36, c_32, c_34, c_34, c_34, c_1852])).
% 7.69/2.56  tff(c_1923, plain, (![B_355, E_356]: (m1_subset_1(k3_tmap_1('#skF_1', B_355, '#skF_1', '#skF_5', E_356), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_355)))) | ~v5_pre_topc(E_356, '#skF_1', B_355) | ~m1_subset_1(E_356, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_355)))) | ~v1_funct_2(E_356, u1_struct_0('#skF_1'), u1_struct_0(B_355)) | ~v1_funct_1(E_356) | ~l1_pre_topc(B_355) | ~v2_pre_topc(B_355) | v2_struct_0(B_355))), inference(negUnitSimplification, [status(thm)], [c_60, c_42, c_38, c_1880])).
% 7.69/2.56  tff(c_1930, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1502, c_1923])).
% 7.69/2.56  tff(c_1935, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_1392, c_1930])).
% 7.69/2.56  tff(c_1937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1393, c_1935])).
% 7.69/2.56  tff(c_1939, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_96])).
% 7.69/2.56  tff(c_1938, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_96])).
% 7.69/2.56  tff(c_1949, plain, (![C_364, B_361, D_363, A_365, E_362]: (k3_tmap_1(A_365, B_361, C_364, D_363, E_362)=k2_partfun1(u1_struct_0(C_364), u1_struct_0(B_361), E_362, u1_struct_0(D_363)) | ~m1_pre_topc(D_363, C_364) | ~m1_subset_1(E_362, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_364), u1_struct_0(B_361)))) | ~v1_funct_2(E_362, u1_struct_0(C_364), u1_struct_0(B_361)) | ~v1_funct_1(E_362) | ~m1_pre_topc(D_363, A_365) | ~m1_pre_topc(C_364, A_365) | ~l1_pre_topc(B_361) | ~v2_pre_topc(B_361) | v2_struct_0(B_361) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.69/2.56  tff(c_1951, plain, (![A_365, D_363]: (k3_tmap_1(A_365, '#skF_2', '#skF_1', D_363, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_363)) | ~m1_pre_topc(D_363, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_363, A_365) | ~m1_pre_topc('#skF_1', A_365) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365))), inference(resolution, [status(thm)], [c_44, c_1949])).
% 7.69/2.56  tff(c_1954, plain, (![A_365, D_363]: (k3_tmap_1(A_365, '#skF_2', '#skF_1', D_363, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_363)) | ~m1_pre_topc(D_363, '#skF_1') | ~m1_pre_topc(D_363, A_365) | ~m1_pre_topc('#skF_1', A_365) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_1951])).
% 7.69/2.56  tff(c_1965, plain, (![A_367, D_368]: (k3_tmap_1(A_367, '#skF_2', '#skF_1', D_368, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_368)) | ~m1_pre_topc(D_368, '#skF_1') | ~m1_pre_topc(D_368, A_367) | ~m1_pre_topc('#skF_1', A_367) | ~l1_pre_topc(A_367) | ~v2_pre_topc(A_367) | v2_struct_0(A_367))), inference(negUnitSimplification, [status(thm)], [c_54, c_1954])).
% 7.69/2.56  tff(c_1969, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1965])).
% 7.69/2.56  tff(c_1975, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_36, c_1969])).
% 7.69/2.56  tff(c_1976, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_1975])).
% 7.69/2.56  tff(c_1981, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_1976])).
% 7.69/2.56  tff(c_1985, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1981])).
% 7.69/2.56  tff(c_1989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1985])).
% 7.69/2.56  tff(c_1990, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_1976])).
% 7.69/2.56  tff(c_1942, plain, (![A_357, B_358, C_359, D_360]: (k2_partfun1(u1_struct_0(A_357), u1_struct_0(B_358), C_359, u1_struct_0(D_360))=k2_tmap_1(A_357, B_358, C_359, D_360) | ~m1_pre_topc(D_360, A_357) | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_357), u1_struct_0(B_358)))) | ~v1_funct_2(C_359, u1_struct_0(A_357), u1_struct_0(B_358)) | ~v1_funct_1(C_359) | ~l1_pre_topc(B_358) | ~v2_pre_topc(B_358) | v2_struct_0(B_358) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357) | v2_struct_0(A_357))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.69/2.56  tff(c_1944, plain, (![D_360]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_360))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_360) | ~m1_pre_topc(D_360, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_1942])).
% 7.69/2.56  tff(c_1947, plain, (![D_360]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_360))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_360) | ~m1_pre_topc(D_360, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_1944])).
% 7.69/2.56  tff(c_1948, plain, (![D_360]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_360))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_360) | ~m1_pre_topc(D_360, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_1947])).
% 7.69/2.56  tff(c_2001, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1990, c_1948])).
% 7.69/2.56  tff(c_2008, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2001])).
% 7.69/2.56  tff(c_2264, plain, (![C_408, E_409, B_407, D_410, A_406]: (v1_funct_2(k3_tmap_1(A_406, B_407, k1_tsep_1(A_406, C_408, D_410), D_410, E_409), u1_struct_0(D_410), u1_struct_0(B_407)) | ~v5_pre_topc(E_409, k1_tsep_1(A_406, C_408, D_410), B_407) | ~m1_subset_1(E_409, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_406, C_408, D_410)), u1_struct_0(B_407)))) | ~v1_funct_2(E_409, u1_struct_0(k1_tsep_1(A_406, C_408, D_410)), u1_struct_0(B_407)) | ~v1_funct_1(E_409) | ~r4_tsep_1(A_406, C_408, D_410) | ~m1_pre_topc(D_410, A_406) | v2_struct_0(D_410) | ~m1_pre_topc(C_408, A_406) | v2_struct_0(C_408) | ~l1_pre_topc(B_407) | ~v2_pre_topc(B_407) | v2_struct_0(B_407) | ~l1_pre_topc(A_406) | ~v2_pre_topc(A_406) | v2_struct_0(A_406))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.69/2.56  tff(c_2266, plain, (![B_407, E_409]: (v1_funct_2(k3_tmap_1('#skF_1', B_407, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_409), u1_struct_0('#skF_5'), u1_struct_0(B_407)) | ~v5_pre_topc(E_409, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_407) | ~m1_subset_1(E_409, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_407)))) | ~v1_funct_2(E_409, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_407)) | ~v1_funct_1(E_409) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_407) | ~v2_pre_topc(B_407) | v2_struct_0(B_407) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2264])).
% 7.69/2.56  tff(c_2268, plain, (![B_407, E_409]: (v1_funct_2(k3_tmap_1('#skF_1', B_407, '#skF_1', '#skF_5', E_409), u1_struct_0('#skF_5'), u1_struct_0(B_407)) | ~v5_pre_topc(E_409, '#skF_1', B_407) | ~m1_subset_1(E_409, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_407)))) | ~v1_funct_2(E_409, u1_struct_0('#skF_1'), u1_struct_0(B_407)) | ~v1_funct_1(E_409) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_407) | ~v2_pre_topc(B_407) | v2_struct_0(B_407) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_36, c_32, c_34, c_34, c_34, c_2266])).
% 7.69/2.56  tff(c_2339, plain, (![B_416, E_417]: (v1_funct_2(k3_tmap_1('#skF_1', B_416, '#skF_1', '#skF_5', E_417), u1_struct_0('#skF_5'), u1_struct_0(B_416)) | ~v5_pre_topc(E_417, '#skF_1', B_416) | ~m1_subset_1(E_417, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_416)))) | ~v1_funct_2(E_417, u1_struct_0('#skF_1'), u1_struct_0(B_416)) | ~v1_funct_1(E_417) | ~l1_pre_topc(B_416) | ~v2_pre_topc(B_416) | v2_struct_0(B_416))), inference(negUnitSimplification, [status(thm)], [c_60, c_42, c_38, c_2268])).
% 7.69/2.56  tff(c_2344, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_2339])).
% 7.69/2.56  tff(c_2350, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_1938, c_2008, c_2344])).
% 7.69/2.56  tff(c_2352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1939, c_2350])).
% 7.69/2.56  tff(c_2354, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_136])).
% 7.69/2.56  tff(c_2353, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_136])).
% 7.69/2.56  tff(c_2374, plain, (![A_427, E_424, D_425, C_426, B_423]: (k3_tmap_1(A_427, B_423, C_426, D_425, E_424)=k2_partfun1(u1_struct_0(C_426), u1_struct_0(B_423), E_424, u1_struct_0(D_425)) | ~m1_pre_topc(D_425, C_426) | ~m1_subset_1(E_424, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_426), u1_struct_0(B_423)))) | ~v1_funct_2(E_424, u1_struct_0(C_426), u1_struct_0(B_423)) | ~v1_funct_1(E_424) | ~m1_pre_topc(D_425, A_427) | ~m1_pre_topc(C_426, A_427) | ~l1_pre_topc(B_423) | ~v2_pre_topc(B_423) | v2_struct_0(B_423) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.69/2.56  tff(c_2376, plain, (![A_427, D_425]: (k3_tmap_1(A_427, '#skF_2', '#skF_1', D_425, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_425)) | ~m1_pre_topc(D_425, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_425, A_427) | ~m1_pre_topc('#skF_1', A_427) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(resolution, [status(thm)], [c_44, c_2374])).
% 7.69/2.56  tff(c_2379, plain, (![A_427, D_425]: (k3_tmap_1(A_427, '#skF_2', '#skF_1', D_425, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_425)) | ~m1_pre_topc(D_425, '#skF_1') | ~m1_pre_topc(D_425, A_427) | ~m1_pre_topc('#skF_1', A_427) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_2376])).
% 7.69/2.56  tff(c_2387, plain, (![A_433, D_434]: (k3_tmap_1(A_433, '#skF_2', '#skF_1', D_434, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_434)) | ~m1_pre_topc(D_434, '#skF_1') | ~m1_pre_topc(D_434, A_433) | ~m1_pre_topc('#skF_1', A_433) | ~l1_pre_topc(A_433) | ~v2_pre_topc(A_433) | v2_struct_0(A_433))), inference(negUnitSimplification, [status(thm)], [c_54, c_2379])).
% 7.69/2.56  tff(c_2391, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2387])).
% 7.69/2.56  tff(c_2397, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_36, c_2391])).
% 7.69/2.56  tff(c_2398, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_2397])).
% 7.69/2.56  tff(c_2403, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_2398])).
% 7.69/2.56  tff(c_2406, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2403])).
% 7.69/2.56  tff(c_2410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_2406])).
% 7.69/2.56  tff(c_2412, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_2398])).
% 7.69/2.56  tff(c_2393, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2387])).
% 7.69/2.56  tff(c_2401, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_2393])).
% 7.69/2.56  tff(c_2402, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_2401])).
% 7.69/2.56  tff(c_2413, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_2402])).
% 7.69/2.56  tff(c_2421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2412, c_2413])).
% 7.69/2.56  tff(c_2422, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_2402])).
% 7.69/2.56  tff(c_2358, plain, (![A_418, B_419, C_420, D_421]: (k2_partfun1(u1_struct_0(A_418), u1_struct_0(B_419), C_420, u1_struct_0(D_421))=k2_tmap_1(A_418, B_419, C_420, D_421) | ~m1_pre_topc(D_421, A_418) | ~m1_subset_1(C_420, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_418), u1_struct_0(B_419)))) | ~v1_funct_2(C_420, u1_struct_0(A_418), u1_struct_0(B_419)) | ~v1_funct_1(C_420) | ~l1_pre_topc(B_419) | ~v2_pre_topc(B_419) | v2_struct_0(B_419) | ~l1_pre_topc(A_418) | ~v2_pre_topc(A_418) | v2_struct_0(A_418))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.69/2.56  tff(c_2360, plain, (![D_421]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_421))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_421) | ~m1_pre_topc(D_421, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_2358])).
% 7.69/2.56  tff(c_2363, plain, (![D_421]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_421))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_421) | ~m1_pre_topc(D_421, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_2360])).
% 7.69/2.56  tff(c_2364, plain, (![D_421]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_421))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_421) | ~m1_pre_topc(D_421, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_2363])).
% 7.69/2.56  tff(c_2434, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2422, c_2364])).
% 7.69/2.56  tff(c_2441, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2434])).
% 7.69/2.56  tff(c_2674, plain, (![A_460, D_464, B_461, E_463, C_462]: (v1_funct_2(k3_tmap_1(A_460, B_461, k1_tsep_1(A_460, C_462, D_464), C_462, E_463), u1_struct_0(C_462), u1_struct_0(B_461)) | ~v5_pre_topc(E_463, k1_tsep_1(A_460, C_462, D_464), B_461) | ~m1_subset_1(E_463, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_460, C_462, D_464)), u1_struct_0(B_461)))) | ~v1_funct_2(E_463, u1_struct_0(k1_tsep_1(A_460, C_462, D_464)), u1_struct_0(B_461)) | ~v1_funct_1(E_463) | ~r4_tsep_1(A_460, C_462, D_464) | ~m1_pre_topc(D_464, A_460) | v2_struct_0(D_464) | ~m1_pre_topc(C_462, A_460) | v2_struct_0(C_462) | ~l1_pre_topc(B_461) | ~v2_pre_topc(B_461) | v2_struct_0(B_461) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.69/2.56  tff(c_2676, plain, (![B_461, E_463]: (v1_funct_2(k3_tmap_1('#skF_1', B_461, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_463), u1_struct_0('#skF_4'), u1_struct_0(B_461)) | ~v5_pre_topc(E_463, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_461) | ~m1_subset_1(E_463, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_461)))) | ~v1_funct_2(E_463, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_461)) | ~v1_funct_1(E_463) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_461) | ~v2_pre_topc(B_461) | v2_struct_0(B_461) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2674])).
% 7.69/2.56  tff(c_2678, plain, (![B_461, E_463]: (v1_funct_2(k3_tmap_1('#skF_1', B_461, '#skF_1', '#skF_4', E_463), u1_struct_0('#skF_4'), u1_struct_0(B_461)) | ~v5_pre_topc(E_463, '#skF_1', B_461) | ~m1_subset_1(E_463, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_461)))) | ~v1_funct_2(E_463, u1_struct_0('#skF_1'), u1_struct_0(B_461)) | ~v1_funct_1(E_463) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_461) | ~v2_pre_topc(B_461) | v2_struct_0(B_461) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_36, c_32, c_34, c_34, c_34, c_2676])).
% 7.69/2.56  tff(c_2680, plain, (![B_465, E_466]: (v1_funct_2(k3_tmap_1('#skF_1', B_465, '#skF_1', '#skF_4', E_466), u1_struct_0('#skF_4'), u1_struct_0(B_465)) | ~v5_pre_topc(E_466, '#skF_1', B_465) | ~m1_subset_1(E_466, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_465)))) | ~v1_funct_2(E_466, u1_struct_0('#skF_1'), u1_struct_0(B_465)) | ~v1_funct_1(E_466) | ~l1_pre_topc(B_465) | ~v2_pre_topc(B_465) | v2_struct_0(B_465))), inference(negUnitSimplification, [status(thm)], [c_60, c_42, c_38, c_2678])).
% 7.69/2.56  tff(c_2682, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_2680])).
% 7.69/2.56  tff(c_2685, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_2353, c_2441, c_2682])).
% 7.69/2.56  tff(c_2687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2354, c_2685])).
% 7.69/2.56  tff(c_2689, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_86])).
% 7.69/2.56  tff(c_2688, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_86])).
% 7.69/2.56  tff(c_2710, plain, (![A_476, B_472, D_474, E_473, C_475]: (k3_tmap_1(A_476, B_472, C_475, D_474, E_473)=k2_partfun1(u1_struct_0(C_475), u1_struct_0(B_472), E_473, u1_struct_0(D_474)) | ~m1_pre_topc(D_474, C_475) | ~m1_subset_1(E_473, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_475), u1_struct_0(B_472)))) | ~v1_funct_2(E_473, u1_struct_0(C_475), u1_struct_0(B_472)) | ~v1_funct_1(E_473) | ~m1_pre_topc(D_474, A_476) | ~m1_pre_topc(C_475, A_476) | ~l1_pre_topc(B_472) | ~v2_pre_topc(B_472) | v2_struct_0(B_472) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.69/2.56  tff(c_2712, plain, (![A_476, D_474]: (k3_tmap_1(A_476, '#skF_2', '#skF_1', D_474, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_474)) | ~m1_pre_topc(D_474, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_474, A_476) | ~m1_pre_topc('#skF_1', A_476) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(resolution, [status(thm)], [c_44, c_2710])).
% 7.69/2.56  tff(c_2715, plain, (![A_476, D_474]: (k3_tmap_1(A_476, '#skF_2', '#skF_1', D_474, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_474)) | ~m1_pre_topc(D_474, '#skF_1') | ~m1_pre_topc(D_474, A_476) | ~m1_pre_topc('#skF_1', A_476) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_2712])).
% 7.69/2.56  tff(c_2717, plain, (![A_477, D_478]: (k3_tmap_1(A_477, '#skF_2', '#skF_1', D_478, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_478)) | ~m1_pre_topc(D_478, '#skF_1') | ~m1_pre_topc(D_478, A_477) | ~m1_pre_topc('#skF_1', A_477) | ~l1_pre_topc(A_477) | ~v2_pre_topc(A_477) | v2_struct_0(A_477))), inference(negUnitSimplification, [status(thm)], [c_54, c_2715])).
% 7.69/2.56  tff(c_2721, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2717])).
% 7.69/2.56  tff(c_2727, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_36, c_2721])).
% 7.69/2.56  tff(c_2728, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_2727])).
% 7.69/2.56  tff(c_2733, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_2728])).
% 7.69/2.56  tff(c_2742, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2733])).
% 7.69/2.56  tff(c_2746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_2742])).
% 7.69/2.56  tff(c_2747, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_2728])).
% 7.69/2.56  tff(c_2694, plain, (![A_467, B_468, C_469, D_470]: (k2_partfun1(u1_struct_0(A_467), u1_struct_0(B_468), C_469, u1_struct_0(D_470))=k2_tmap_1(A_467, B_468, C_469, D_470) | ~m1_pre_topc(D_470, A_467) | ~m1_subset_1(C_469, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_467), u1_struct_0(B_468)))) | ~v1_funct_2(C_469, u1_struct_0(A_467), u1_struct_0(B_468)) | ~v1_funct_1(C_469) | ~l1_pre_topc(B_468) | ~v2_pre_topc(B_468) | v2_struct_0(B_468) | ~l1_pre_topc(A_467) | ~v2_pre_topc(A_467) | v2_struct_0(A_467))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.69/2.56  tff(c_2696, plain, (![D_470]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_470))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_470) | ~m1_pre_topc(D_470, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_2694])).
% 7.69/2.56  tff(c_2699, plain, (![D_470]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_470))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_470) | ~m1_pre_topc(D_470, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_2696])).
% 7.69/2.56  tff(c_2700, plain, (![D_470]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_470))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_470) | ~m1_pre_topc(D_470, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_2699])).
% 7.69/2.56  tff(c_2758, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2747, c_2700])).
% 7.69/2.56  tff(c_2765, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2758])).
% 7.69/2.56  tff(c_2993, plain, (![D_511, A_507, B_508, C_509, E_510]: (v5_pre_topc(k3_tmap_1(A_507, B_508, k1_tsep_1(A_507, C_509, D_511), D_511, E_510), D_511, B_508) | ~v5_pre_topc(E_510, k1_tsep_1(A_507, C_509, D_511), B_508) | ~m1_subset_1(E_510, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_507, C_509, D_511)), u1_struct_0(B_508)))) | ~v1_funct_2(E_510, u1_struct_0(k1_tsep_1(A_507, C_509, D_511)), u1_struct_0(B_508)) | ~v1_funct_1(E_510) | ~r4_tsep_1(A_507, C_509, D_511) | ~m1_pre_topc(D_511, A_507) | v2_struct_0(D_511) | ~m1_pre_topc(C_509, A_507) | v2_struct_0(C_509) | ~l1_pre_topc(B_508) | ~v2_pre_topc(B_508) | v2_struct_0(B_508) | ~l1_pre_topc(A_507) | ~v2_pre_topc(A_507) | v2_struct_0(A_507))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.69/2.56  tff(c_2995, plain, (![B_508, E_510]: (v5_pre_topc(k3_tmap_1('#skF_1', B_508, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_510), '#skF_5', B_508) | ~v5_pre_topc(E_510, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_508) | ~m1_subset_1(E_510, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_508)))) | ~v1_funct_2(E_510, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_508)) | ~v1_funct_1(E_510) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_508) | ~v2_pre_topc(B_508) | v2_struct_0(B_508) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2993])).
% 7.69/2.56  tff(c_2997, plain, (![B_508, E_510]: (v5_pre_topc(k3_tmap_1('#skF_1', B_508, '#skF_1', '#skF_5', E_510), '#skF_5', B_508) | ~v5_pre_topc(E_510, '#skF_1', B_508) | ~m1_subset_1(E_510, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_508)))) | ~v1_funct_2(E_510, u1_struct_0('#skF_1'), u1_struct_0(B_508)) | ~v1_funct_1(E_510) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_508) | ~v2_pre_topc(B_508) | v2_struct_0(B_508) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_36, c_32, c_34, c_34, c_34, c_2995])).
% 7.69/2.56  tff(c_2999, plain, (![B_512, E_513]: (v5_pre_topc(k3_tmap_1('#skF_1', B_512, '#skF_1', '#skF_5', E_513), '#skF_5', B_512) | ~v5_pre_topc(E_513, '#skF_1', B_512) | ~m1_subset_1(E_513, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_512)))) | ~v1_funct_2(E_513, u1_struct_0('#skF_1'), u1_struct_0(B_512)) | ~v1_funct_1(E_513) | ~l1_pre_topc(B_512) | ~v2_pre_topc(B_512) | v2_struct_0(B_512))), inference(negUnitSimplification, [status(thm)], [c_60, c_42, c_38, c_2997])).
% 7.69/2.56  tff(c_3001, plain, (v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), '#skF_5', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_2999])).
% 7.69/2.56  tff(c_3004, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_2688, c_2765, c_3001])).
% 7.69/2.56  tff(c_3006, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2689, c_3004])).
% 7.69/2.56  tff(c_3008, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_126])).
% 7.69/2.56  tff(c_3007, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_126])).
% 7.69/2.56  tff(c_3030, plain, (![E_520, D_521, A_523, C_522, B_519]: (k3_tmap_1(A_523, B_519, C_522, D_521, E_520)=k2_partfun1(u1_struct_0(C_522), u1_struct_0(B_519), E_520, u1_struct_0(D_521)) | ~m1_pre_topc(D_521, C_522) | ~m1_subset_1(E_520, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_522), u1_struct_0(B_519)))) | ~v1_funct_2(E_520, u1_struct_0(C_522), u1_struct_0(B_519)) | ~v1_funct_1(E_520) | ~m1_pre_topc(D_521, A_523) | ~m1_pre_topc(C_522, A_523) | ~l1_pre_topc(B_519) | ~v2_pre_topc(B_519) | v2_struct_0(B_519) | ~l1_pre_topc(A_523) | ~v2_pre_topc(A_523) | v2_struct_0(A_523))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.69/2.56  tff(c_3032, plain, (![A_523, D_521]: (k3_tmap_1(A_523, '#skF_2', '#skF_1', D_521, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_521)) | ~m1_pre_topc(D_521, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_521, A_523) | ~m1_pre_topc('#skF_1', A_523) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_523) | ~v2_pre_topc(A_523) | v2_struct_0(A_523))), inference(resolution, [status(thm)], [c_44, c_3030])).
% 7.69/2.56  tff(c_3035, plain, (![A_523, D_521]: (k3_tmap_1(A_523, '#skF_2', '#skF_1', D_521, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_521)) | ~m1_pre_topc(D_521, '#skF_1') | ~m1_pre_topc(D_521, A_523) | ~m1_pre_topc('#skF_1', A_523) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_523) | ~v2_pre_topc(A_523) | v2_struct_0(A_523))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_3032])).
% 7.69/2.56  tff(c_3037, plain, (![A_524, D_525]: (k3_tmap_1(A_524, '#skF_2', '#skF_1', D_525, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_525)) | ~m1_pre_topc(D_525, '#skF_1') | ~m1_pre_topc(D_525, A_524) | ~m1_pre_topc('#skF_1', A_524) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524))), inference(negUnitSimplification, [status(thm)], [c_54, c_3035])).
% 7.69/2.56  tff(c_3041, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_3037])).
% 7.69/2.56  tff(c_3047, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_36, c_3041])).
% 7.69/2.56  tff(c_3048, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_3047])).
% 7.69/2.56  tff(c_3053, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3048])).
% 7.69/2.56  tff(c_3056, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_3053])).
% 7.69/2.56  tff(c_3060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_3056])).
% 7.69/2.56  tff(c_3062, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_3048])).
% 7.69/2.56  tff(c_3043, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_3037])).
% 7.69/2.56  tff(c_3051, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_3043])).
% 7.69/2.56  tff(c_3052, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_3051])).
% 7.69/2.56  tff(c_3131, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3062, c_3052])).
% 7.69/2.56  tff(c_3014, plain, (![A_514, B_515, C_516, D_517]: (k2_partfun1(u1_struct_0(A_514), u1_struct_0(B_515), C_516, u1_struct_0(D_517))=k2_tmap_1(A_514, B_515, C_516, D_517) | ~m1_pre_topc(D_517, A_514) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_514), u1_struct_0(B_515)))) | ~v1_funct_2(C_516, u1_struct_0(A_514), u1_struct_0(B_515)) | ~v1_funct_1(C_516) | ~l1_pre_topc(B_515) | ~v2_pre_topc(B_515) | v2_struct_0(B_515) | ~l1_pre_topc(A_514) | ~v2_pre_topc(A_514) | v2_struct_0(A_514))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.69/2.56  tff(c_3016, plain, (![D_517]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_517))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_517) | ~m1_pre_topc(D_517, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_3014])).
% 7.69/2.56  tff(c_3019, plain, (![D_517]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_517))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_517) | ~m1_pre_topc(D_517, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_3016])).
% 7.69/2.56  tff(c_3020, plain, (![D_517]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_517))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_517) | ~m1_pre_topc(D_517, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_3019])).
% 7.69/2.56  tff(c_3135, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3131, c_3020])).
% 7.69/2.56  tff(c_3142, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3135])).
% 7.69/2.56  tff(c_3307, plain, (![C_551, A_549, E_552, B_550, D_553]: (v5_pre_topc(k3_tmap_1(A_549, B_550, k1_tsep_1(A_549, C_551, D_553), C_551, E_552), C_551, B_550) | ~v5_pre_topc(E_552, k1_tsep_1(A_549, C_551, D_553), B_550) | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_549, C_551, D_553)), u1_struct_0(B_550)))) | ~v1_funct_2(E_552, u1_struct_0(k1_tsep_1(A_549, C_551, D_553)), u1_struct_0(B_550)) | ~v1_funct_1(E_552) | ~r4_tsep_1(A_549, C_551, D_553) | ~m1_pre_topc(D_553, A_549) | v2_struct_0(D_553) | ~m1_pre_topc(C_551, A_549) | v2_struct_0(C_551) | ~l1_pre_topc(B_550) | ~v2_pre_topc(B_550) | v2_struct_0(B_550) | ~l1_pre_topc(A_549) | ~v2_pre_topc(A_549) | v2_struct_0(A_549))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.69/2.56  tff(c_3309, plain, (![B_550, E_552]: (v5_pre_topc(k3_tmap_1('#skF_1', B_550, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_552), '#skF_4', B_550) | ~v5_pre_topc(E_552, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_550) | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_550)))) | ~v1_funct_2(E_552, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_550)) | ~v1_funct_1(E_552) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_550) | ~v2_pre_topc(B_550) | v2_struct_0(B_550) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3307])).
% 7.69/2.56  tff(c_3311, plain, (![B_550, E_552]: (v5_pre_topc(k3_tmap_1('#skF_1', B_550, '#skF_1', '#skF_4', E_552), '#skF_4', B_550) | ~v5_pre_topc(E_552, '#skF_1', B_550) | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_550)))) | ~v1_funct_2(E_552, u1_struct_0('#skF_1'), u1_struct_0(B_550)) | ~v1_funct_1(E_552) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_550) | ~v2_pre_topc(B_550) | v2_struct_0(B_550) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_36, c_32, c_34, c_34, c_34, c_3309])).
% 7.69/2.56  tff(c_3313, plain, (![B_554, E_555]: (v5_pre_topc(k3_tmap_1('#skF_1', B_554, '#skF_1', '#skF_4', E_555), '#skF_4', B_554) | ~v5_pre_topc(E_555, '#skF_1', B_554) | ~m1_subset_1(E_555, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_554)))) | ~v1_funct_2(E_555, u1_struct_0('#skF_1'), u1_struct_0(B_554)) | ~v1_funct_1(E_555) | ~l1_pre_topc(B_554) | ~v2_pre_topc(B_554) | v2_struct_0(B_554))), inference(negUnitSimplification, [status(thm)], [c_60, c_42, c_38, c_3311])).
% 7.69/2.56  tff(c_3315, plain, (v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_3313])).
% 7.69/2.56  tff(c_3318, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_3007, c_3142, c_3315])).
% 7.69/2.56  tff(c_3320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_3008, c_3318])).
% 7.69/2.56  tff(c_3322, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_106])).
% 7.69/2.56  tff(c_3321, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_106])).
% 7.69/2.56  tff(c_3345, plain, (![D_563, C_564, B_561, A_565, E_562]: (k3_tmap_1(A_565, B_561, C_564, D_563, E_562)=k2_partfun1(u1_struct_0(C_564), u1_struct_0(B_561), E_562, u1_struct_0(D_563)) | ~m1_pre_topc(D_563, C_564) | ~m1_subset_1(E_562, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_564), u1_struct_0(B_561)))) | ~v1_funct_2(E_562, u1_struct_0(C_564), u1_struct_0(B_561)) | ~v1_funct_1(E_562) | ~m1_pre_topc(D_563, A_565) | ~m1_pre_topc(C_564, A_565) | ~l1_pre_topc(B_561) | ~v2_pre_topc(B_561) | v2_struct_0(B_561) | ~l1_pre_topc(A_565) | ~v2_pre_topc(A_565) | v2_struct_0(A_565))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.69/2.56  tff(c_3347, plain, (![A_565, D_563]: (k3_tmap_1(A_565, '#skF_2', '#skF_1', D_563, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_563)) | ~m1_pre_topc(D_563, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_563, A_565) | ~m1_pre_topc('#skF_1', A_565) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_565) | ~v2_pre_topc(A_565) | v2_struct_0(A_565))), inference(resolution, [status(thm)], [c_44, c_3345])).
% 7.69/2.56  tff(c_3350, plain, (![A_565, D_563]: (k3_tmap_1(A_565, '#skF_2', '#skF_1', D_563, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_563)) | ~m1_pre_topc(D_563, '#skF_1') | ~m1_pre_topc(D_563, A_565) | ~m1_pre_topc('#skF_1', A_565) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_565) | ~v2_pre_topc(A_565) | v2_struct_0(A_565))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_3347])).
% 7.69/2.56  tff(c_3352, plain, (![A_566, D_567]: (k3_tmap_1(A_566, '#skF_2', '#skF_1', D_567, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_567)) | ~m1_pre_topc(D_567, '#skF_1') | ~m1_pre_topc(D_567, A_566) | ~m1_pre_topc('#skF_1', A_566) | ~l1_pre_topc(A_566) | ~v2_pre_topc(A_566) | v2_struct_0(A_566))), inference(negUnitSimplification, [status(thm)], [c_54, c_3350])).
% 7.69/2.56  tff(c_3356, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_3352])).
% 7.69/2.56  tff(c_3362, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_36, c_3356])).
% 7.69/2.56  tff(c_3363, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_3362])).
% 7.69/2.56  tff(c_3368, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3363])).
% 7.69/2.56  tff(c_3377, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_3368])).
% 7.69/2.56  tff(c_3381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_3377])).
% 7.69/2.56  tff(c_3382, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_3363])).
% 7.69/2.56  tff(c_3329, plain, (![A_556, B_557, C_558, D_559]: (k2_partfun1(u1_struct_0(A_556), u1_struct_0(B_557), C_558, u1_struct_0(D_559))=k2_tmap_1(A_556, B_557, C_558, D_559) | ~m1_pre_topc(D_559, A_556) | ~m1_subset_1(C_558, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_556), u1_struct_0(B_557)))) | ~v1_funct_2(C_558, u1_struct_0(A_556), u1_struct_0(B_557)) | ~v1_funct_1(C_558) | ~l1_pre_topc(B_557) | ~v2_pre_topc(B_557) | v2_struct_0(B_557) | ~l1_pre_topc(A_556) | ~v2_pre_topc(A_556) | v2_struct_0(A_556))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.69/2.56  tff(c_3331, plain, (![D_559]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_559))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_559) | ~m1_pre_topc(D_559, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_3329])).
% 7.69/2.56  tff(c_3334, plain, (![D_559]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_559))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_559) | ~m1_pre_topc(D_559, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_3331])).
% 7.69/2.56  tff(c_3335, plain, (![D_559]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_559))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_559) | ~m1_pre_topc(D_559, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_3334])).
% 7.69/2.56  tff(c_3393, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3382, c_3335])).
% 7.69/2.56  tff(c_3400, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3393])).
% 7.69/2.56  tff(c_3574, plain, (![C_583, A_581, D_585, B_582, E_584]: (v1_funct_1(k3_tmap_1(A_581, B_582, k1_tsep_1(A_581, C_583, D_585), D_585, E_584)) | ~v5_pre_topc(E_584, k1_tsep_1(A_581, C_583, D_585), B_582) | ~m1_subset_1(E_584, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_581, C_583, D_585)), u1_struct_0(B_582)))) | ~v1_funct_2(E_584, u1_struct_0(k1_tsep_1(A_581, C_583, D_585)), u1_struct_0(B_582)) | ~v1_funct_1(E_584) | ~r4_tsep_1(A_581, C_583, D_585) | ~m1_pre_topc(D_585, A_581) | v2_struct_0(D_585) | ~m1_pre_topc(C_583, A_581) | v2_struct_0(C_583) | ~l1_pre_topc(B_582) | ~v2_pre_topc(B_582) | v2_struct_0(B_582) | ~l1_pre_topc(A_581) | ~v2_pre_topc(A_581) | v2_struct_0(A_581))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.69/2.56  tff(c_3576, plain, (![B_582, E_584]: (v1_funct_1(k3_tmap_1('#skF_1', B_582, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_584)) | ~v5_pre_topc(E_584, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_582) | ~m1_subset_1(E_584, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_582)))) | ~v1_funct_2(E_584, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_582)) | ~v1_funct_1(E_584) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_582) | ~v2_pre_topc(B_582) | v2_struct_0(B_582) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3574])).
% 7.69/2.56  tff(c_3578, plain, (![B_582, E_584]: (v1_funct_1(k3_tmap_1('#skF_1', B_582, '#skF_1', '#skF_5', E_584)) | ~v5_pre_topc(E_584, '#skF_1', B_582) | ~m1_subset_1(E_584, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_582)))) | ~v1_funct_2(E_584, u1_struct_0('#skF_1'), u1_struct_0(B_582)) | ~v1_funct_1(E_584) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_582) | ~v2_pre_topc(B_582) | v2_struct_0(B_582) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_36, c_32, c_34, c_34, c_34, c_3576])).
% 7.69/2.56  tff(c_3607, plain, (![B_587, E_588]: (v1_funct_1(k3_tmap_1('#skF_1', B_587, '#skF_1', '#skF_5', E_588)) | ~v5_pre_topc(E_588, '#skF_1', B_587) | ~m1_subset_1(E_588, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_587)))) | ~v1_funct_2(E_588, u1_struct_0('#skF_1'), u1_struct_0(B_587)) | ~v1_funct_1(E_588) | ~l1_pre_topc(B_587) | ~v2_pre_topc(B_587) | v2_struct_0(B_587))), inference(negUnitSimplification, [status(thm)], [c_60, c_42, c_38, c_3578])).
% 7.69/2.56  tff(c_3610, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_3607])).
% 7.69/2.56  tff(c_3613, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_3321, c_3400, c_3610])).
% 7.69/2.56  tff(c_3615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_3322, c_3613])).
% 7.69/2.56  tff(c_3617, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_146])).
% 7.69/2.56  tff(c_3616, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_146])).
% 7.69/2.56  tff(c_3641, plain, (![E_595, A_598, B_594, D_596, C_597]: (k3_tmap_1(A_598, B_594, C_597, D_596, E_595)=k2_partfun1(u1_struct_0(C_597), u1_struct_0(B_594), E_595, u1_struct_0(D_596)) | ~m1_pre_topc(D_596, C_597) | ~m1_subset_1(E_595, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_597), u1_struct_0(B_594)))) | ~v1_funct_2(E_595, u1_struct_0(C_597), u1_struct_0(B_594)) | ~v1_funct_1(E_595) | ~m1_pre_topc(D_596, A_598) | ~m1_pre_topc(C_597, A_598) | ~l1_pre_topc(B_594) | ~v2_pre_topc(B_594) | v2_struct_0(B_594) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.69/2.56  tff(c_3643, plain, (![A_598, D_596]: (k3_tmap_1(A_598, '#skF_2', '#skF_1', D_596, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_596)) | ~m1_pre_topc(D_596, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_596, A_598) | ~m1_pre_topc('#skF_1', A_598) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598))), inference(resolution, [status(thm)], [c_44, c_3641])).
% 7.69/2.56  tff(c_3646, plain, (![A_598, D_596]: (k3_tmap_1(A_598, '#skF_2', '#skF_1', D_596, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_596)) | ~m1_pre_topc(D_596, '#skF_1') | ~m1_pre_topc(D_596, A_598) | ~m1_pre_topc('#skF_1', A_598) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_3643])).
% 7.69/2.56  tff(c_3654, plain, (![A_604, D_605]: (k3_tmap_1(A_604, '#skF_2', '#skF_1', D_605, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_605)) | ~m1_pre_topc(D_605, '#skF_1') | ~m1_pre_topc(D_605, A_604) | ~m1_pre_topc('#skF_1', A_604) | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(negUnitSimplification, [status(thm)], [c_54, c_3646])).
% 7.69/2.56  tff(c_3658, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_3654])).
% 7.69/2.56  tff(c_3664, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_36, c_3658])).
% 7.69/2.56  tff(c_3665, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_3664])).
% 7.69/2.56  tff(c_3670, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3665])).
% 7.69/2.56  tff(c_3673, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_3670])).
% 7.69/2.56  tff(c_3677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_3673])).
% 7.69/2.56  tff(c_3679, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_3665])).
% 7.69/2.56  tff(c_3660, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_3654])).
% 7.69/2.56  tff(c_3668, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_3660])).
% 7.69/2.56  tff(c_3669, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_3668])).
% 7.69/2.56  tff(c_3680, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3669])).
% 7.69/2.56  tff(c_3688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3679, c_3680])).
% 7.69/2.56  tff(c_3689, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_3669])).
% 7.69/2.56  tff(c_3625, plain, (![A_589, B_590, C_591, D_592]: (k2_partfun1(u1_struct_0(A_589), u1_struct_0(B_590), C_591, u1_struct_0(D_592))=k2_tmap_1(A_589, B_590, C_591, D_592) | ~m1_pre_topc(D_592, A_589) | ~m1_subset_1(C_591, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_589), u1_struct_0(B_590)))) | ~v1_funct_2(C_591, u1_struct_0(A_589), u1_struct_0(B_590)) | ~v1_funct_1(C_591) | ~l1_pre_topc(B_590) | ~v2_pre_topc(B_590) | v2_struct_0(B_590) | ~l1_pre_topc(A_589) | ~v2_pre_topc(A_589) | v2_struct_0(A_589))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.69/2.56  tff(c_3627, plain, (![D_592]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_592))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_592) | ~m1_pre_topc(D_592, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_3625])).
% 7.69/2.56  tff(c_3630, plain, (![D_592]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_592))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_592) | ~m1_pre_topc(D_592, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_3627])).
% 7.69/2.56  tff(c_3631, plain, (![D_592]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_592))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_592) | ~m1_pre_topc(D_592, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_3630])).
% 7.69/2.56  tff(c_3701, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3689, c_3631])).
% 7.69/2.56  tff(c_3708, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3701])).
% 7.69/2.56  tff(c_3712, plain, (![A_606, D_610, E_609, B_607, C_608]: (v1_funct_1(k3_tmap_1(A_606, B_607, k1_tsep_1(A_606, C_608, D_610), C_608, E_609)) | ~v5_pre_topc(E_609, k1_tsep_1(A_606, C_608, D_610), B_607) | ~m1_subset_1(E_609, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_606, C_608, D_610)), u1_struct_0(B_607)))) | ~v1_funct_2(E_609, u1_struct_0(k1_tsep_1(A_606, C_608, D_610)), u1_struct_0(B_607)) | ~v1_funct_1(E_609) | ~r4_tsep_1(A_606, C_608, D_610) | ~m1_pre_topc(D_610, A_606) | v2_struct_0(D_610) | ~m1_pre_topc(C_608, A_606) | v2_struct_0(C_608) | ~l1_pre_topc(B_607) | ~v2_pre_topc(B_607) | v2_struct_0(B_607) | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606) | v2_struct_0(A_606))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.69/2.56  tff(c_3714, plain, (![B_607, E_609]: (v1_funct_1(k3_tmap_1('#skF_1', B_607, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_609)) | ~v5_pre_topc(E_609, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_607) | ~m1_subset_1(E_609, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_607)))) | ~v1_funct_2(E_609, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_607)) | ~v1_funct_1(E_609) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_607) | ~v2_pre_topc(B_607) | v2_struct_0(B_607) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3712])).
% 7.69/2.56  tff(c_3716, plain, (![B_607, E_609]: (v1_funct_1(k3_tmap_1('#skF_1', B_607, '#skF_1', '#skF_4', E_609)) | ~v5_pre_topc(E_609, '#skF_1', B_607) | ~m1_subset_1(E_609, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_607)))) | ~v1_funct_2(E_609, u1_struct_0('#skF_1'), u1_struct_0(B_607)) | ~v1_funct_1(E_609) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_607) | ~v2_pre_topc(B_607) | v2_struct_0(B_607) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_36, c_32, c_34, c_34, c_34, c_3714])).
% 7.69/2.56  tff(c_3919, plain, (![B_625, E_626]: (v1_funct_1(k3_tmap_1('#skF_1', B_625, '#skF_1', '#skF_4', E_626)) | ~v5_pre_topc(E_626, '#skF_1', B_625) | ~m1_subset_1(E_626, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_625)))) | ~v1_funct_2(E_626, u1_struct_0('#skF_1'), u1_struct_0(B_625)) | ~v1_funct_1(E_626) | ~l1_pre_topc(B_625) | ~v2_pre_topc(B_625) | v2_struct_0(B_625))), inference(negUnitSimplification, [status(thm)], [c_60, c_42, c_38, c_3716])).
% 7.69/2.56  tff(c_3922, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_3919])).
% 7.69/2.56  tff(c_3925, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_3616, c_3708, c_3922])).
% 7.69/2.56  tff(c_3927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_3617, c_3925])).
% 7.69/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.69/2.56  
% 7.69/2.56  Inference rules
% 7.69/2.56  ----------------------
% 7.69/2.56  #Ref     : 0
% 7.69/2.56  #Sup     : 761
% 7.69/2.56  #Fact    : 0
% 7.69/2.56  #Define  : 0
% 7.69/2.56  #Split   : 40
% 7.69/2.56  #Chain   : 0
% 7.69/2.56  #Close   : 0
% 7.69/2.56  
% 7.69/2.56  Ordering : KBO
% 7.69/2.56  
% 7.69/2.56  Simplification rules
% 7.69/2.56  ----------------------
% 7.69/2.56  #Subsume      : 98
% 7.69/2.56  #Demod        : 1457
% 7.69/2.56  #Tautology    : 450
% 7.69/2.56  #SimpNegUnit  : 291
% 7.69/2.56  #BackRed      : 28
% 7.69/2.56  
% 7.69/2.56  #Partial instantiations: 0
% 7.69/2.56  #Strategies tried      : 1
% 7.69/2.56  
% 7.69/2.56  Timing (in seconds)
% 7.69/2.56  ----------------------
% 7.69/2.57  Preprocessing        : 0.43
% 7.69/2.57  Parsing              : 0.22
% 7.69/2.57  CNF conversion       : 0.06
% 7.69/2.57  Main loop            : 1.26
% 7.69/2.57  Inferencing          : 0.44
% 7.69/2.57  Reduction            : 0.41
% 7.69/2.57  Demodulation         : 0.29
% 7.69/2.57  BG Simplification    : 0.06
% 7.69/2.57  Subsumption          : 0.29
% 7.69/2.57  Abstraction          : 0.07
% 7.69/2.57  MUC search           : 0.00
% 7.69/2.57  Cooper               : 0.00
% 7.69/2.57  Total                : 1.80
% 7.69/2.57  Index Insertion      : 0.00
% 7.69/2.57  Index Deletion       : 0.00
% 7.69/2.57  Index Matching       : 0.00
% 7.69/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
