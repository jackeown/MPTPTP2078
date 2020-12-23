%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:08 EST 2020

% Result     : Theorem 7.27s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :  399 (2656 expanded)
%              Number of leaves         :   31 (1084 expanded)
%              Depth                    :   14
%              Number of atoms          : 2111 (33360 expanded)
%              Number of equality atoms :  148 (1466 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

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

tff(f_232,negated_conjecture,(
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
                      & v1_tsep_1(D,A)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( ~ v2_struct_0(E)
                          & v1_tsep_1(E,A)
                          & m1_pre_topc(E,A) )
                       => ( A = k1_tsep_1(A,D,E)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_tmap_1)).

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

tff(f_167,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_tsep_1(C,A)
                & m1_pre_topc(C,A) )
             => r4_tsep_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tsep_1)).

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

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_150,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_190,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_140,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_194,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_130,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_193,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_120,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_197,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_110,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_191,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_100,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_195,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_90,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_192,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_80,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_196,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_66,plain,
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
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_164,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_66])).

tff(c_174,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_164])).

tff(c_184,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_174])).

tff(c_660,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_194,c_193,c_197,c_191,c_195,c_192,c_196,c_184])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_30,plain,(
    ! [A_78] :
      ( m1_pre_topc(A_78,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_36,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_218,plain,(
    ! [E_121,A_124,D_122,B_120,C_123] :
      ( k3_tmap_1(A_124,B_120,C_123,D_122,E_121) = k2_partfun1(u1_struct_0(C_123),u1_struct_0(B_120),E_121,u1_struct_0(D_122))
      | ~ m1_pre_topc(D_122,C_123)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_123),u1_struct_0(B_120))))
      | ~ v1_funct_2(E_121,u1_struct_0(C_123),u1_struct_0(B_120))
      | ~ v1_funct_1(E_121)
      | ~ m1_pre_topc(D_122,A_124)
      | ~ m1_pre_topc(C_123,A_124)
      | ~ l1_pre_topc(B_120)
      | ~ v2_pre_topc(B_120)
      | v2_struct_0(B_120)
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_224,plain,(
    ! [A_124,D_122] :
      ( k3_tmap_1(A_124,'#skF_2','#skF_1',D_122,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_122))
      | ~ m1_pre_topc(D_122,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_122,A_124)
      | ~ m1_pre_topc('#skF_1',A_124)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_48,c_218])).

tff(c_235,plain,(
    ! [A_124,D_122] :
      ( k3_tmap_1(A_124,'#skF_2','#skF_1',D_122,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_122))
      | ~ m1_pre_topc(D_122,'#skF_1')
      | ~ m1_pre_topc(D_122,A_124)
      | ~ m1_pre_topc('#skF_1',A_124)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_224])).

tff(c_248,plain,(
    ! [A_126,D_127] :
      ( k3_tmap_1(A_126,'#skF_2','#skF_1',D_127,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_127))
      | ~ m1_pre_topc(D_127,'#skF_1')
      | ~ m1_pre_topc(D_127,A_126)
      | ~ m1_pre_topc('#skF_1',A_126)
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_235])).

tff(c_252,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_248])).

tff(c_258,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_36,c_252])).

tff(c_259,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_258])).

tff(c_264,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_267,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_264])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_267])).

tff(c_273,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_254,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_248])).

tff(c_262,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_254])).

tff(c_263,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_262])).

tff(c_359,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_263])).

tff(c_199,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k2_partfun1(u1_struct_0(A_116),u1_struct_0(B_117),C_118,u1_struct_0(D_119)) = k2_tmap_1(A_116,B_117,C_118,D_119)
      | ~ m1_pre_topc(D_119,A_116)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116),u1_struct_0(B_117))))
      | ~ v1_funct_2(C_118,u1_struct_0(A_116),u1_struct_0(B_117))
      | ~ v1_funct_1(C_118)
      | ~ l1_pre_topc(B_117)
      | ~ v2_pre_topc(B_117)
      | v2_struct_0(B_117)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_205,plain,(
    ! [D_119] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_119)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_119)
      | ~ m1_pre_topc(D_119,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_199])).

tff(c_216,plain,(
    ! [D_119] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_119)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_119)
      | ~ m1_pre_topc(D_119,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_205])).

tff(c_217,plain,(
    ! [D_119] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_119)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_119)
      | ~ m1_pre_topc(D_119,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_216])).

tff(c_363,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_217])).

tff(c_370,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_363])).

tff(c_272,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_289,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_217])).

tff(c_296,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_289])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_44,plain,(
    v1_tsep_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_38,plain,(
    v1_tsep_1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_32,plain,(
    ! [A_79,B_83,C_85] :
      ( r4_tsep_1(A_79,B_83,C_85)
      | ~ m1_pre_topc(C_85,A_79)
      | ~ v1_tsep_1(C_85,A_79)
      | ~ m1_pre_topc(B_83,A_79)
      | ~ v1_tsep_1(B_83,A_79)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_34,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_280,plain,(
    ! [B_129,C_130,A_128,D_132,E_131] :
      ( v1_funct_1(k3_tmap_1(A_128,B_129,k1_tsep_1(A_128,C_130,D_132),D_132,E_131))
      | ~ v5_pre_topc(E_131,k1_tsep_1(A_128,C_130,D_132),B_129)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_128,C_130,D_132)),u1_struct_0(B_129))))
      | ~ v1_funct_2(E_131,u1_struct_0(k1_tsep_1(A_128,C_130,D_132)),u1_struct_0(B_129))
      | ~ v1_funct_1(E_131)
      | ~ r4_tsep_1(A_128,C_130,D_132)
      | ~ m1_pre_topc(D_132,A_128)
      | v2_struct_0(D_132)
      | ~ m1_pre_topc(C_130,A_128)
      | v2_struct_0(C_130)
      | ~ l1_pre_topc(B_129)
      | ~ v2_pre_topc(B_129)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_282,plain,(
    ! [B_129,E_131] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_129,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_131))
      | ~ v5_pre_topc(E_131,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_129)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_129))))
      | ~ v1_funct_2(E_131,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_129))
      | ~ v1_funct_1(E_131)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_129)
      | ~ v2_pre_topc(B_129)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_280])).

tff(c_284,plain,(
    ! [B_129,E_131] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_129,'#skF_1','#skF_5',E_131))
      | ~ v5_pre_topc(E_131,'#skF_1',B_129)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_129))))
      | ~ v1_funct_2(E_131,u1_struct_0('#skF_1'),u1_struct_0(B_129))
      | ~ v1_funct_1(E_131)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_129)
      | ~ v2_pre_topc(B_129)
      | v2_struct_0(B_129)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_34,c_34,c_34,c_282])).

tff(c_285,plain,(
    ! [B_129,E_131] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_129,'#skF_1','#skF_5',E_131))
      | ~ v5_pre_topc(E_131,'#skF_1',B_129)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_129))))
      | ~ v1_funct_2(E_131,u1_struct_0('#skF_1'),u1_struct_0(B_129))
      | ~ v1_funct_1(E_131)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ l1_pre_topc(B_129)
      | ~ v2_pre_topc(B_129)
      | v2_struct_0(B_129) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_284])).

tff(c_402,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_405,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_tsep_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_402])).

tff(c_408,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_42,c_38,c_36,c_405])).

tff(c_410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_408])).

tff(c_412,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_838,plain,(
    ! [E_197,C_196,A_194,D_198,B_195] :
      ( v5_pre_topc(E_197,k1_tsep_1(A_194,C_196,D_198),B_195)
      | ~ m1_subset_1(k3_tmap_1(A_194,B_195,k1_tsep_1(A_194,C_196,D_198),D_198,E_197),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_198),u1_struct_0(B_195))))
      | ~ v5_pre_topc(k3_tmap_1(A_194,B_195,k1_tsep_1(A_194,C_196,D_198),D_198,E_197),D_198,B_195)
      | ~ v1_funct_2(k3_tmap_1(A_194,B_195,k1_tsep_1(A_194,C_196,D_198),D_198,E_197),u1_struct_0(D_198),u1_struct_0(B_195))
      | ~ v1_funct_1(k3_tmap_1(A_194,B_195,k1_tsep_1(A_194,C_196,D_198),D_198,E_197))
      | ~ m1_subset_1(k3_tmap_1(A_194,B_195,k1_tsep_1(A_194,C_196,D_198),C_196,E_197),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_196),u1_struct_0(B_195))))
      | ~ v5_pre_topc(k3_tmap_1(A_194,B_195,k1_tsep_1(A_194,C_196,D_198),C_196,E_197),C_196,B_195)
      | ~ v1_funct_2(k3_tmap_1(A_194,B_195,k1_tsep_1(A_194,C_196,D_198),C_196,E_197),u1_struct_0(C_196),u1_struct_0(B_195))
      | ~ v1_funct_1(k3_tmap_1(A_194,B_195,k1_tsep_1(A_194,C_196,D_198),C_196,E_197))
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_194,C_196,D_198)),u1_struct_0(B_195))))
      | ~ v1_funct_2(E_197,u1_struct_0(k1_tsep_1(A_194,C_196,D_198)),u1_struct_0(B_195))
      | ~ v1_funct_1(E_197)
      | ~ r4_tsep_1(A_194,C_196,D_198)
      | ~ m1_pre_topc(D_198,A_194)
      | v2_struct_0(D_198)
      | ~ m1_pre_topc(C_196,A_194)
      | v2_struct_0(C_196)
      | ~ l1_pre_topc(B_195)
      | ~ v2_pre_topc(B_195)
      | v2_struct_0(B_195)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_845,plain,(
    ! [E_197,B_195] :
      ( v5_pre_topc(E_197,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_195)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_195,'#skF_1','#skF_5',E_197),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_195))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_195,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_197),'#skF_5',B_195)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_195,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_197),u1_struct_0('#skF_5'),u1_struct_0(B_195))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_195,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_197))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_195,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_197),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_195))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_195,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_197),'#skF_4',B_195)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_195,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_197),u1_struct_0('#skF_4'),u1_struct_0(B_195))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_195,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_197))
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_195))))
      | ~ v1_funct_2(E_197,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_195))
      | ~ v1_funct_1(E_197)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_195)
      | ~ v2_pre_topc(B_195)
      | v2_struct_0(B_195)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_838])).

tff(c_849,plain,(
    ! [E_197,B_195] :
      ( v5_pre_topc(E_197,'#skF_1',B_195)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_195,'#skF_1','#skF_5',E_197),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_195))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_195,'#skF_1','#skF_5',E_197),'#skF_5',B_195)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_195,'#skF_1','#skF_5',E_197),u1_struct_0('#skF_5'),u1_struct_0(B_195))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_195,'#skF_1','#skF_5',E_197))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_195,'#skF_1','#skF_4',E_197),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_195))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_195,'#skF_1','#skF_4',E_197),'#skF_4',B_195)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_195,'#skF_1','#skF_4',E_197),u1_struct_0('#skF_4'),u1_struct_0(B_195))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_195,'#skF_1','#skF_4',E_197))
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_195))))
      | ~ v1_funct_2(E_197,u1_struct_0('#skF_1'),u1_struct_0(B_195))
      | ~ v1_funct_1(E_197)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_195)
      | ~ v2_pre_topc(B_195)
      | v2_struct_0(B_195)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_412,c_34,c_34,c_34,c_34,c_34,c_34,c_34,c_34,c_34,c_34,c_845])).

tff(c_907,plain,(
    ! [E_225,B_226] :
      ( v5_pre_topc(E_225,'#skF_1',B_226)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_226,'#skF_1','#skF_5',E_225),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_226))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_226,'#skF_1','#skF_5',E_225),'#skF_5',B_226)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_226,'#skF_1','#skF_5',E_225),u1_struct_0('#skF_5'),u1_struct_0(B_226))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_226,'#skF_1','#skF_5',E_225))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_226,'#skF_1','#skF_4',E_225),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_226))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_226,'#skF_1','#skF_4',E_225),'#skF_4',B_226)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_226,'#skF_1','#skF_4',E_225),u1_struct_0('#skF_4'),u1_struct_0(B_226))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_226,'#skF_1','#skF_4',E_225))
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_226))))
      | ~ v1_funct_2(E_225,u1_struct_0('#skF_1'),u1_struct_0(B_226))
      | ~ v1_funct_1(E_225)
      | ~ l1_pre_topc(B_226)
      | ~ v2_pre_topc(B_226)
      | v2_struct_0(B_226) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_849])).

tff(c_913,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_296,c_907])).

tff(c_916,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_190,c_370,c_194,c_370,c_193,c_370,c_197,c_370,c_191,c_296,c_195,c_296,c_192,c_296,c_196,c_913])).

tff(c_918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_660,c_916])).

tff(c_920,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_919,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_945,plain,(
    ! [C_238,A_239,D_237,E_236,B_235] :
      ( k3_tmap_1(A_239,B_235,C_238,D_237,E_236) = k2_partfun1(u1_struct_0(C_238),u1_struct_0(B_235),E_236,u1_struct_0(D_237))
      | ~ m1_pre_topc(D_237,C_238)
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_238),u1_struct_0(B_235))))
      | ~ v1_funct_2(E_236,u1_struct_0(C_238),u1_struct_0(B_235))
      | ~ v1_funct_1(E_236)
      | ~ m1_pre_topc(D_237,A_239)
      | ~ m1_pre_topc(C_238,A_239)
      | ~ l1_pre_topc(B_235)
      | ~ v2_pre_topc(B_235)
      | v2_struct_0(B_235)
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_949,plain,(
    ! [A_239,D_237] :
      ( k3_tmap_1(A_239,'#skF_2','#skF_1',D_237,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_237))
      | ~ m1_pre_topc(D_237,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_237,A_239)
      | ~ m1_pre_topc('#skF_1',A_239)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(resolution,[status(thm)],[c_48,c_945])).

tff(c_956,plain,(
    ! [A_239,D_237] :
      ( k3_tmap_1(A_239,'#skF_2','#skF_1',D_237,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_237))
      | ~ m1_pre_topc(D_237,'#skF_1')
      | ~ m1_pre_topc(D_237,A_239)
      | ~ m1_pre_topc('#skF_1',A_239)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_949])).

tff(c_958,plain,(
    ! [A_240,D_241] :
      ( k3_tmap_1(A_240,'#skF_2','#skF_1',D_241,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_241))
      | ~ m1_pre_topc(D_241,'#skF_1')
      | ~ m1_pre_topc(D_241,A_240)
      | ~ m1_pre_topc('#skF_1',A_240)
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_956])).

tff(c_962,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_958])).

tff(c_968,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_36,c_962])).

tff(c_969,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_968])).

tff(c_974,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_969])).

tff(c_977,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_974])).

tff(c_981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_977])).

tff(c_983,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_969])).

tff(c_964,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_958])).

tff(c_972,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_964])).

tff(c_973,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_972])).

tff(c_1075,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_973])).

tff(c_922,plain,(
    ! [A_230,B_231,C_232,D_233] :
      ( k2_partfun1(u1_struct_0(A_230),u1_struct_0(B_231),C_232,u1_struct_0(D_233)) = k2_tmap_1(A_230,B_231,C_232,D_233)
      | ~ m1_pre_topc(D_233,A_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_230),u1_struct_0(B_231))))
      | ~ v1_funct_2(C_232,u1_struct_0(A_230),u1_struct_0(B_231))
      | ~ v1_funct_1(C_232)
      | ~ l1_pre_topc(B_231)
      | ~ v2_pre_topc(B_231)
      | v2_struct_0(B_231)
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_926,plain,(
    ! [D_233] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_233)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_233)
      | ~ m1_pre_topc(D_233,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_922])).

tff(c_933,plain,(
    ! [D_233] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_233)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_233)
      | ~ m1_pre_topc(D_233,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_926])).

tff(c_934,plain,(
    ! [D_233] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_233)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_233)
      | ~ m1_pre_topc(D_233,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_933])).

tff(c_1079,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1075,c_934])).

tff(c_1086,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1079])).

tff(c_984,plain,(
    ! [C_244,E_245,B_243,A_242,D_246] :
      ( v1_funct_1(k3_tmap_1(A_242,B_243,k1_tsep_1(A_242,C_244,D_246),D_246,E_245))
      | ~ v5_pre_topc(E_245,k1_tsep_1(A_242,C_244,D_246),B_243)
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_242,C_244,D_246)),u1_struct_0(B_243))))
      | ~ v1_funct_2(E_245,u1_struct_0(k1_tsep_1(A_242,C_244,D_246)),u1_struct_0(B_243))
      | ~ v1_funct_1(E_245)
      | ~ r4_tsep_1(A_242,C_244,D_246)
      | ~ m1_pre_topc(D_246,A_242)
      | v2_struct_0(D_246)
      | ~ m1_pre_topc(C_244,A_242)
      | v2_struct_0(C_244)
      | ~ l1_pre_topc(B_243)
      | ~ v2_pre_topc(B_243)
      | v2_struct_0(B_243)
      | ~ l1_pre_topc(A_242)
      | ~ v2_pre_topc(A_242)
      | v2_struct_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_986,plain,(
    ! [B_243,E_245] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_243,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_245))
      | ~ v5_pre_topc(E_245,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_243)
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_243))))
      | ~ v1_funct_2(E_245,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_243))
      | ~ v1_funct_1(E_245)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_243)
      | ~ v2_pre_topc(B_243)
      | v2_struct_0(B_243)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_984])).

tff(c_988,plain,(
    ! [B_243,E_245] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_243,'#skF_1','#skF_5',E_245))
      | ~ v5_pre_topc(E_245,'#skF_1',B_243)
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_243))))
      | ~ v1_funct_2(E_245,u1_struct_0('#skF_1'),u1_struct_0(B_243))
      | ~ v1_funct_1(E_245)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_243)
      | ~ v2_pre_topc(B_243)
      | v2_struct_0(B_243)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_34,c_34,c_34,c_986])).

tff(c_989,plain,(
    ! [B_243,E_245] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_243,'#skF_1','#skF_5',E_245))
      | ~ v5_pre_topc(E_245,'#skF_1',B_243)
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_243))))
      | ~ v1_funct_2(E_245,u1_struct_0('#skF_1'),u1_struct_0(B_243))
      | ~ v1_funct_1(E_245)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ l1_pre_topc(B_243)
      | ~ v2_pre_topc(B_243)
      | v2_struct_0(B_243) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_988])).

tff(c_1096,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_989])).

tff(c_1099,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_tsep_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1096])).

tff(c_1102,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_42,c_38,c_36,c_1099])).

tff(c_1104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1102])).

tff(c_1106,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_989])).

tff(c_1331,plain,(
    ! [B_292,C_293,D_295,A_291,E_294] :
      ( m1_subset_1(k3_tmap_1(A_291,B_292,k1_tsep_1(A_291,C_293,D_295),C_293,E_294),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_293),u1_struct_0(B_292))))
      | ~ v5_pre_topc(E_294,k1_tsep_1(A_291,C_293,D_295),B_292)
      | ~ m1_subset_1(E_294,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_291,C_293,D_295)),u1_struct_0(B_292))))
      | ~ v1_funct_2(E_294,u1_struct_0(k1_tsep_1(A_291,C_293,D_295)),u1_struct_0(B_292))
      | ~ v1_funct_1(E_294)
      | ~ r4_tsep_1(A_291,C_293,D_295)
      | ~ m1_pre_topc(D_295,A_291)
      | v2_struct_0(D_295)
      | ~ m1_pre_topc(C_293,A_291)
      | v2_struct_0(C_293)
      | ~ l1_pre_topc(B_292)
      | ~ v2_pre_topc(B_292)
      | v2_struct_0(B_292)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1376,plain,(
    ! [B_292,E_294] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_292,'#skF_1','#skF_4',E_294),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_292))))
      | ~ v5_pre_topc(E_294,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_292)
      | ~ m1_subset_1(E_294,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_292))))
      | ~ v1_funct_2(E_294,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_292))
      | ~ v1_funct_1(E_294)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_292)
      | ~ v2_pre_topc(B_292)
      | v2_struct_0(B_292)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1331])).

tff(c_1404,plain,(
    ! [B_292,E_294] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_292,'#skF_1','#skF_4',E_294),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_292))))
      | ~ v5_pre_topc(E_294,'#skF_1',B_292)
      | ~ m1_subset_1(E_294,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_292))))
      | ~ v1_funct_2(E_294,u1_struct_0('#skF_1'),u1_struct_0(B_292))
      | ~ v1_funct_1(E_294)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_292)
      | ~ v2_pre_topc(B_292)
      | v2_struct_0(B_292)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_1106,c_34,c_34,c_34,c_1376])).

tff(c_1406,plain,(
    ! [B_296,E_297] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_296,'#skF_1','#skF_4',E_297),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_296))))
      | ~ v5_pre_topc(E_297,'#skF_1',B_296)
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_296))))
      | ~ v1_funct_2(E_297,u1_struct_0('#skF_1'),u1_struct_0(B_296))
      | ~ v1_funct_1(E_297)
      | ~ l1_pre_topc(B_296)
      | ~ v2_pre_topc(B_296)
      | v2_struct_0(B_296) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_1404])).

tff(c_1413,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_1406])).

tff(c_1418,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_919,c_1413])).

tff(c_1420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_920,c_1418])).

tff(c_1422,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1421,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1441,plain,(
    ! [D_308,B_306,E_307,A_310,C_309] :
      ( k3_tmap_1(A_310,B_306,C_309,D_308,E_307) = k2_partfun1(u1_struct_0(C_309),u1_struct_0(B_306),E_307,u1_struct_0(D_308))
      | ~ m1_pre_topc(D_308,C_309)
      | ~ m1_subset_1(E_307,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_309),u1_struct_0(B_306))))
      | ~ v1_funct_2(E_307,u1_struct_0(C_309),u1_struct_0(B_306))
      | ~ v1_funct_1(E_307)
      | ~ m1_pre_topc(D_308,A_310)
      | ~ m1_pre_topc(C_309,A_310)
      | ~ l1_pre_topc(B_306)
      | ~ v2_pre_topc(B_306)
      | v2_struct_0(B_306)
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310)
      | v2_struct_0(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1443,plain,(
    ! [A_310,D_308] :
      ( k3_tmap_1(A_310,'#skF_2','#skF_1',D_308,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_308))
      | ~ m1_pre_topc(D_308,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_308,A_310)
      | ~ m1_pre_topc('#skF_1',A_310)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310)
      | v2_struct_0(A_310) ) ),
    inference(resolution,[status(thm)],[c_48,c_1441])).

tff(c_1446,plain,(
    ! [A_310,D_308] :
      ( k3_tmap_1(A_310,'#skF_2','#skF_1',D_308,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_308))
      | ~ m1_pre_topc(D_308,'#skF_1')
      | ~ m1_pre_topc(D_308,A_310)
      | ~ m1_pre_topc('#skF_1',A_310)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310)
      | v2_struct_0(A_310) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_1443])).

tff(c_1448,plain,(
    ! [A_311,D_312] :
      ( k3_tmap_1(A_311,'#skF_2','#skF_1',D_312,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_312))
      | ~ m1_pre_topc(D_312,'#skF_1')
      | ~ m1_pre_topc(D_312,A_311)
      | ~ m1_pre_topc('#skF_1',A_311)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311)
      | v2_struct_0(A_311) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1446])).

tff(c_1452,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1448])).

tff(c_1458,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_36,c_1452])).

tff(c_1459,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1458])).

tff(c_1464,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1459])).

tff(c_1467,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1464])).

tff(c_1471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1467])).

tff(c_1472,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1459])).

tff(c_1425,plain,(
    ! [A_301,B_302,C_303,D_304] :
      ( k2_partfun1(u1_struct_0(A_301),u1_struct_0(B_302),C_303,u1_struct_0(D_304)) = k2_tmap_1(A_301,B_302,C_303,D_304)
      | ~ m1_pre_topc(D_304,A_301)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_301),u1_struct_0(B_302))))
      | ~ v1_funct_2(C_303,u1_struct_0(A_301),u1_struct_0(B_302))
      | ~ v1_funct_1(C_303)
      | ~ l1_pre_topc(B_302)
      | ~ v2_pre_topc(B_302)
      | v2_struct_0(B_302)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1427,plain,(
    ! [D_304] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_304)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_304)
      | ~ m1_pre_topc(D_304,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_1425])).

tff(c_1430,plain,(
    ! [D_304] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_304)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_304)
      | ~ m1_pre_topc(D_304,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_1427])).

tff(c_1431,plain,(
    ! [D_304] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_304)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_304)
      | ~ m1_pre_topc(D_304,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_1430])).

tff(c_1489,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1472,c_1431])).

tff(c_1496,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1489])).

tff(c_1480,plain,(
    ! [D_317,C_315,B_314,E_316,A_313] :
      ( v1_funct_1(k3_tmap_1(A_313,B_314,k1_tsep_1(A_313,C_315,D_317),D_317,E_316))
      | ~ v5_pre_topc(E_316,k1_tsep_1(A_313,C_315,D_317),B_314)
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_313,C_315,D_317)),u1_struct_0(B_314))))
      | ~ v1_funct_2(E_316,u1_struct_0(k1_tsep_1(A_313,C_315,D_317)),u1_struct_0(B_314))
      | ~ v1_funct_1(E_316)
      | ~ r4_tsep_1(A_313,C_315,D_317)
      | ~ m1_pre_topc(D_317,A_313)
      | v2_struct_0(D_317)
      | ~ m1_pre_topc(C_315,A_313)
      | v2_struct_0(C_315)
      | ~ l1_pre_topc(B_314)
      | ~ v2_pre_topc(B_314)
      | v2_struct_0(B_314)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1482,plain,(
    ! [B_314,E_316] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_314,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_316))
      | ~ v5_pre_topc(E_316,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_314)
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_314))))
      | ~ v1_funct_2(E_316,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_314))
      | ~ v1_funct_1(E_316)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_314)
      | ~ v2_pre_topc(B_314)
      | v2_struct_0(B_314)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1480])).

tff(c_1484,plain,(
    ! [B_314,E_316] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_314,'#skF_1','#skF_5',E_316))
      | ~ v5_pre_topc(E_316,'#skF_1',B_314)
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_314))))
      | ~ v1_funct_2(E_316,u1_struct_0('#skF_1'),u1_struct_0(B_314))
      | ~ v1_funct_1(E_316)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_314)
      | ~ v2_pre_topc(B_314)
      | v2_struct_0(B_314)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_34,c_34,c_34,c_1482])).

tff(c_1485,plain,(
    ! [B_314,E_316] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_314,'#skF_1','#skF_5',E_316))
      | ~ v5_pre_topc(E_316,'#skF_1',B_314)
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_314))))
      | ~ v1_funct_2(E_316,u1_struct_0('#skF_1'),u1_struct_0(B_314))
      | ~ v1_funct_1(E_316)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ l1_pre_topc(B_314)
      | ~ v2_pre_topc(B_314)
      | v2_struct_0(B_314) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_1484])).

tff(c_1602,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1485])).

tff(c_1605,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_tsep_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1602])).

tff(c_1608,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_42,c_38,c_36,c_1605])).

tff(c_1610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1608])).

tff(c_1612,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1485])).

tff(c_1873,plain,(
    ! [A_364,D_368,E_367,C_366,B_365] :
      ( m1_subset_1(k3_tmap_1(A_364,B_365,k1_tsep_1(A_364,C_366,D_368),D_368,E_367),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_368),u1_struct_0(B_365))))
      | ~ v5_pre_topc(E_367,k1_tsep_1(A_364,C_366,D_368),B_365)
      | ~ m1_subset_1(E_367,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_364,C_366,D_368)),u1_struct_0(B_365))))
      | ~ v1_funct_2(E_367,u1_struct_0(k1_tsep_1(A_364,C_366,D_368)),u1_struct_0(B_365))
      | ~ v1_funct_1(E_367)
      | ~ r4_tsep_1(A_364,C_366,D_368)
      | ~ m1_pre_topc(D_368,A_364)
      | v2_struct_0(D_368)
      | ~ m1_pre_topc(C_366,A_364)
      | v2_struct_0(C_366)
      | ~ l1_pre_topc(B_365)
      | ~ v2_pre_topc(B_365)
      | v2_struct_0(B_365)
      | ~ l1_pre_topc(A_364)
      | ~ v2_pre_topc(A_364)
      | v2_struct_0(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1918,plain,(
    ! [B_365,E_367] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_365,'#skF_1','#skF_5',E_367),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_365))))
      | ~ v5_pre_topc(E_367,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_365)
      | ~ m1_subset_1(E_367,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_365))))
      | ~ v1_funct_2(E_367,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_365))
      | ~ v1_funct_1(E_367)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_365)
      | ~ v2_pre_topc(B_365)
      | v2_struct_0(B_365)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1873])).

tff(c_1946,plain,(
    ! [B_365,E_367] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_365,'#skF_1','#skF_5',E_367),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_365))))
      | ~ v5_pre_topc(E_367,'#skF_1',B_365)
      | ~ m1_subset_1(E_367,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_365))))
      | ~ v1_funct_2(E_367,u1_struct_0('#skF_1'),u1_struct_0(B_365))
      | ~ v1_funct_1(E_367)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_365)
      | ~ v2_pre_topc(B_365)
      | v2_struct_0(B_365)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_1612,c_34,c_34,c_34,c_1918])).

tff(c_1963,plain,(
    ! [B_371,E_372] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_371,'#skF_1','#skF_5',E_372),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_371))))
      | ~ v5_pre_topc(E_372,'#skF_1',B_371)
      | ~ m1_subset_1(E_372,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_371))))
      | ~ v1_funct_2(E_372,u1_struct_0('#skF_1'),u1_struct_0(B_371))
      | ~ v1_funct_1(E_372)
      | ~ l1_pre_topc(B_371)
      | ~ v2_pre_topc(B_371)
      | v2_struct_0(B_371) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_1946])).

tff(c_1970,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_1963])).

tff(c_1975,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_1421,c_1970])).

tff(c_1977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1422,c_1975])).

tff(c_1979,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_1978,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_1999,plain,(
    ! [D_383,A_385,B_381,E_382,C_384] :
      ( k3_tmap_1(A_385,B_381,C_384,D_383,E_382) = k2_partfun1(u1_struct_0(C_384),u1_struct_0(B_381),E_382,u1_struct_0(D_383))
      | ~ m1_pre_topc(D_383,C_384)
      | ~ m1_subset_1(E_382,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_384),u1_struct_0(B_381))))
      | ~ v1_funct_2(E_382,u1_struct_0(C_384),u1_struct_0(B_381))
      | ~ v1_funct_1(E_382)
      | ~ m1_pre_topc(D_383,A_385)
      | ~ m1_pre_topc(C_384,A_385)
      | ~ l1_pre_topc(B_381)
      | ~ v2_pre_topc(B_381)
      | v2_struct_0(B_381)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2001,plain,(
    ! [A_385,D_383] :
      ( k3_tmap_1(A_385,'#skF_2','#skF_1',D_383,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_383))
      | ~ m1_pre_topc(D_383,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_383,A_385)
      | ~ m1_pre_topc('#skF_1',A_385)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(resolution,[status(thm)],[c_48,c_1999])).

tff(c_2004,plain,(
    ! [A_385,D_383] :
      ( k3_tmap_1(A_385,'#skF_2','#skF_1',D_383,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_383))
      | ~ m1_pre_topc(D_383,'#skF_1')
      | ~ m1_pre_topc(D_383,A_385)
      | ~ m1_pre_topc('#skF_1',A_385)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2001])).

tff(c_2006,plain,(
    ! [A_386,D_387] :
      ( k3_tmap_1(A_386,'#skF_2','#skF_1',D_387,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_387))
      | ~ m1_pre_topc(D_387,'#skF_1')
      | ~ m1_pre_topc(D_387,A_386)
      | ~ m1_pre_topc('#skF_1',A_386)
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | v2_struct_0(A_386) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2004])).

tff(c_2010,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2006])).

tff(c_2016,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_36,c_2010])).

tff(c_2017,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2016])).

tff(c_2022,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2017])).

tff(c_2025,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2022])).

tff(c_2029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2025])).

tff(c_2030,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2017])).

tff(c_1983,plain,(
    ! [A_376,B_377,C_378,D_379] :
      ( k2_partfun1(u1_struct_0(A_376),u1_struct_0(B_377),C_378,u1_struct_0(D_379)) = k2_tmap_1(A_376,B_377,C_378,D_379)
      | ~ m1_pre_topc(D_379,A_376)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_376),u1_struct_0(B_377))))
      | ~ v1_funct_2(C_378,u1_struct_0(A_376),u1_struct_0(B_377))
      | ~ v1_funct_1(C_378)
      | ~ l1_pre_topc(B_377)
      | ~ v2_pre_topc(B_377)
      | v2_struct_0(B_377)
      | ~ l1_pre_topc(A_376)
      | ~ v2_pre_topc(A_376)
      | v2_struct_0(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1985,plain,(
    ! [D_379] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_379)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_379)
      | ~ m1_pre_topc(D_379,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_1983])).

tff(c_1988,plain,(
    ! [D_379] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_379)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_379)
      | ~ m1_pre_topc(D_379,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_1985])).

tff(c_1989,plain,(
    ! [D_379] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_379)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_379)
      | ~ m1_pre_topc(D_379,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_1988])).

tff(c_2131,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2030,c_1989])).

tff(c_2138,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2131])).

tff(c_2147,plain,(
    ! [B_394,D_397,A_393,E_396,C_395] :
      ( v1_funct_1(k3_tmap_1(A_393,B_394,k1_tsep_1(A_393,C_395,D_397),C_395,E_396))
      | ~ v5_pre_topc(E_396,k1_tsep_1(A_393,C_395,D_397),B_394)
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_393,C_395,D_397)),u1_struct_0(B_394))))
      | ~ v1_funct_2(E_396,u1_struct_0(k1_tsep_1(A_393,C_395,D_397)),u1_struct_0(B_394))
      | ~ v1_funct_1(E_396)
      | ~ r4_tsep_1(A_393,C_395,D_397)
      | ~ m1_pre_topc(D_397,A_393)
      | v2_struct_0(D_397)
      | ~ m1_pre_topc(C_395,A_393)
      | v2_struct_0(C_395)
      | ~ l1_pre_topc(B_394)
      | ~ v2_pre_topc(B_394)
      | v2_struct_0(B_394)
      | ~ l1_pre_topc(A_393)
      | ~ v2_pre_topc(A_393)
      | v2_struct_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2149,plain,(
    ! [B_394,E_396] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_394,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_396))
      | ~ v5_pre_topc(E_396,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_394)
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_394))))
      | ~ v1_funct_2(E_396,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_394))
      | ~ v1_funct_1(E_396)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_394)
      | ~ v2_pre_topc(B_394)
      | v2_struct_0(B_394)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2147])).

tff(c_2151,plain,(
    ! [B_394,E_396] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_394,'#skF_1','#skF_4',E_396))
      | ~ v5_pre_topc(E_396,'#skF_1',B_394)
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_394))))
      | ~ v1_funct_2(E_396,u1_struct_0('#skF_1'),u1_struct_0(B_394))
      | ~ v1_funct_1(E_396)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_394)
      | ~ v2_pre_topc(B_394)
      | v2_struct_0(B_394)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_34,c_34,c_34,c_2149])).

tff(c_2152,plain,(
    ! [B_394,E_396] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_394,'#skF_1','#skF_4',E_396))
      | ~ v5_pre_topc(E_396,'#skF_1',B_394)
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_394))))
      | ~ v1_funct_2(E_396,u1_struct_0('#skF_1'),u1_struct_0(B_394))
      | ~ v1_funct_1(E_396)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ l1_pre_topc(B_394)
      | ~ v2_pre_topc(B_394)
      | v2_struct_0(B_394) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_2151])).

tff(c_2263,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2152])).

tff(c_2267,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_tsep_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2263])).

tff(c_2270,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_42,c_38,c_36,c_2267])).

tff(c_2272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2270])).

tff(c_2274,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2152])).

tff(c_2330,plain,(
    ! [C_427,D_429,A_425,B_426,E_428] :
      ( v1_funct_2(k3_tmap_1(A_425,B_426,k1_tsep_1(A_425,C_427,D_429),D_429,E_428),u1_struct_0(D_429),u1_struct_0(B_426))
      | ~ v5_pre_topc(E_428,k1_tsep_1(A_425,C_427,D_429),B_426)
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_425,C_427,D_429)),u1_struct_0(B_426))))
      | ~ v1_funct_2(E_428,u1_struct_0(k1_tsep_1(A_425,C_427,D_429)),u1_struct_0(B_426))
      | ~ v1_funct_1(E_428)
      | ~ r4_tsep_1(A_425,C_427,D_429)
      | ~ m1_pre_topc(D_429,A_425)
      | v2_struct_0(D_429)
      | ~ m1_pre_topc(C_427,A_425)
      | v2_struct_0(C_427)
      | ~ l1_pre_topc(B_426)
      | ~ v2_pre_topc(B_426)
      | v2_struct_0(B_426)
      | ~ l1_pre_topc(A_425)
      | ~ v2_pre_topc(A_425)
      | v2_struct_0(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2332,plain,(
    ! [B_426,E_428] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_426,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_428),u1_struct_0('#skF_5'),u1_struct_0(B_426))
      | ~ v5_pre_topc(E_428,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_426)
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_426))))
      | ~ v1_funct_2(E_428,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_426))
      | ~ v1_funct_1(E_428)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_426)
      | ~ v2_pre_topc(B_426)
      | v2_struct_0(B_426)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2330])).

tff(c_2334,plain,(
    ! [B_426,E_428] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_426,'#skF_1','#skF_5',E_428),u1_struct_0('#skF_5'),u1_struct_0(B_426))
      | ~ v5_pre_topc(E_428,'#skF_1',B_426)
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_426))))
      | ~ v1_funct_2(E_428,u1_struct_0('#skF_1'),u1_struct_0(B_426))
      | ~ v1_funct_1(E_428)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_426)
      | ~ v2_pre_topc(B_426)
      | v2_struct_0(B_426)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_2274,c_34,c_34,c_34,c_2332])).

tff(c_2336,plain,(
    ! [B_430,E_431] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_430,'#skF_1','#skF_5',E_431),u1_struct_0('#skF_5'),u1_struct_0(B_430))
      | ~ v5_pre_topc(E_431,'#skF_1',B_430)
      | ~ m1_subset_1(E_431,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_430))))
      | ~ v1_funct_2(E_431,u1_struct_0('#skF_1'),u1_struct_0(B_430))
      | ~ v1_funct_1(E_431)
      | ~ l1_pre_topc(B_430)
      | ~ v2_pre_topc(B_430)
      | v2_struct_0(B_430) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_2334])).

tff(c_2338,plain,
    ( v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2336])).

tff(c_2341,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_1978,c_2138,c_2338])).

tff(c_2343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1979,c_2341])).

tff(c_2345,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_2344,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_2366,plain,(
    ! [C_443,B_440,A_444,E_441,D_442] :
      ( k3_tmap_1(A_444,B_440,C_443,D_442,E_441) = k2_partfun1(u1_struct_0(C_443),u1_struct_0(B_440),E_441,u1_struct_0(D_442))
      | ~ m1_pre_topc(D_442,C_443)
      | ~ m1_subset_1(E_441,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_443),u1_struct_0(B_440))))
      | ~ v1_funct_2(E_441,u1_struct_0(C_443),u1_struct_0(B_440))
      | ~ v1_funct_1(E_441)
      | ~ m1_pre_topc(D_442,A_444)
      | ~ m1_pre_topc(C_443,A_444)
      | ~ l1_pre_topc(B_440)
      | ~ v2_pre_topc(B_440)
      | v2_struct_0(B_440)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2368,plain,(
    ! [A_444,D_442] :
      ( k3_tmap_1(A_444,'#skF_2','#skF_1',D_442,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_442))
      | ~ m1_pre_topc(D_442,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_442,A_444)
      | ~ m1_pre_topc('#skF_1',A_444)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(resolution,[status(thm)],[c_48,c_2366])).

tff(c_2371,plain,(
    ! [A_444,D_442] :
      ( k3_tmap_1(A_444,'#skF_2','#skF_1',D_442,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_442))
      | ~ m1_pre_topc(D_442,'#skF_1')
      | ~ m1_pre_topc(D_442,A_444)
      | ~ m1_pre_topc('#skF_1',A_444)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2368])).

tff(c_2373,plain,(
    ! [A_445,D_446] :
      ( k3_tmap_1(A_445,'#skF_2','#skF_1',D_446,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_446))
      | ~ m1_pre_topc(D_446,'#skF_1')
      | ~ m1_pre_topc(D_446,A_445)
      | ~ m1_pre_topc('#skF_1',A_445)
      | ~ l1_pre_topc(A_445)
      | ~ v2_pre_topc(A_445)
      | v2_struct_0(A_445) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2371])).

tff(c_2377,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2373])).

tff(c_2383,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_36,c_2377])).

tff(c_2384,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2383])).

tff(c_2389,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2384])).

tff(c_2392,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2389])).

tff(c_2396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2392])).

tff(c_2398,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2384])).

tff(c_2379,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2373])).

tff(c_2387,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_2379])).

tff(c_2388,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2387])).

tff(c_2484,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_2388])).

tff(c_2350,plain,(
    ! [A_435,B_436,C_437,D_438] :
      ( k2_partfun1(u1_struct_0(A_435),u1_struct_0(B_436),C_437,u1_struct_0(D_438)) = k2_tmap_1(A_435,B_436,C_437,D_438)
      | ~ m1_pre_topc(D_438,A_435)
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_435),u1_struct_0(B_436))))
      | ~ v1_funct_2(C_437,u1_struct_0(A_435),u1_struct_0(B_436))
      | ~ v1_funct_1(C_437)
      | ~ l1_pre_topc(B_436)
      | ~ v2_pre_topc(B_436)
      | v2_struct_0(B_436)
      | ~ l1_pre_topc(A_435)
      | ~ v2_pre_topc(A_435)
      | v2_struct_0(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2352,plain,(
    ! [D_438] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_438)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_438)
      | ~ m1_pre_topc(D_438,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_2350])).

tff(c_2355,plain,(
    ! [D_438] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_438)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_438)
      | ~ m1_pre_topc(D_438,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_2352])).

tff(c_2356,plain,(
    ! [D_438] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_438)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_438)
      | ~ m1_pre_topc(D_438,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_2355])).

tff(c_2488,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2484,c_2356])).

tff(c_2495,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2488])).

tff(c_2405,plain,(
    ! [A_447,D_451,B_448,C_449,E_450] :
      ( v1_funct_1(k3_tmap_1(A_447,B_448,k1_tsep_1(A_447,C_449,D_451),C_449,E_450))
      | ~ v5_pre_topc(E_450,k1_tsep_1(A_447,C_449,D_451),B_448)
      | ~ m1_subset_1(E_450,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_447,C_449,D_451)),u1_struct_0(B_448))))
      | ~ v1_funct_2(E_450,u1_struct_0(k1_tsep_1(A_447,C_449,D_451)),u1_struct_0(B_448))
      | ~ v1_funct_1(E_450)
      | ~ r4_tsep_1(A_447,C_449,D_451)
      | ~ m1_pre_topc(D_451,A_447)
      | v2_struct_0(D_451)
      | ~ m1_pre_topc(C_449,A_447)
      | v2_struct_0(C_449)
      | ~ l1_pre_topc(B_448)
      | ~ v2_pre_topc(B_448)
      | v2_struct_0(B_448)
      | ~ l1_pre_topc(A_447)
      | ~ v2_pre_topc(A_447)
      | v2_struct_0(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2407,plain,(
    ! [B_448,E_450] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_448,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_450))
      | ~ v5_pre_topc(E_450,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_448)
      | ~ m1_subset_1(E_450,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_448))))
      | ~ v1_funct_2(E_450,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_448))
      | ~ v1_funct_1(E_450)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_448)
      | ~ v2_pre_topc(B_448)
      | v2_struct_0(B_448)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2405])).

tff(c_2409,plain,(
    ! [B_448,E_450] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_448,'#skF_1','#skF_4',E_450))
      | ~ v5_pre_topc(E_450,'#skF_1',B_448)
      | ~ m1_subset_1(E_450,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_448))))
      | ~ v1_funct_2(E_450,u1_struct_0('#skF_1'),u1_struct_0(B_448))
      | ~ v1_funct_1(E_450)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_448)
      | ~ v2_pre_topc(B_448)
      | v2_struct_0(B_448)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_34,c_34,c_34,c_2407])).

tff(c_2410,plain,(
    ! [B_448,E_450] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_448,'#skF_1','#skF_4',E_450))
      | ~ v5_pre_topc(E_450,'#skF_1',B_448)
      | ~ m1_subset_1(E_450,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_448))))
      | ~ v1_funct_2(E_450,u1_struct_0('#skF_1'),u1_struct_0(B_448))
      | ~ v1_funct_1(E_450)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ l1_pre_topc(B_448)
      | ~ v2_pre_topc(B_448)
      | v2_struct_0(B_448) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_2409])).

tff(c_2527,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2410])).

tff(c_2530,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_tsep_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2527])).

tff(c_2533,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_42,c_38,c_36,c_2530])).

tff(c_2535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2533])).

tff(c_2537,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2410])).

tff(c_2669,plain,(
    ! [C_479,D_481,B_478,E_480,A_477] :
      ( v1_funct_2(k3_tmap_1(A_477,B_478,k1_tsep_1(A_477,C_479,D_481),C_479,E_480),u1_struct_0(C_479),u1_struct_0(B_478))
      | ~ v5_pre_topc(E_480,k1_tsep_1(A_477,C_479,D_481),B_478)
      | ~ m1_subset_1(E_480,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_477,C_479,D_481)),u1_struct_0(B_478))))
      | ~ v1_funct_2(E_480,u1_struct_0(k1_tsep_1(A_477,C_479,D_481)),u1_struct_0(B_478))
      | ~ v1_funct_1(E_480)
      | ~ r4_tsep_1(A_477,C_479,D_481)
      | ~ m1_pre_topc(D_481,A_477)
      | v2_struct_0(D_481)
      | ~ m1_pre_topc(C_479,A_477)
      | v2_struct_0(C_479)
      | ~ l1_pre_topc(B_478)
      | ~ v2_pre_topc(B_478)
      | v2_struct_0(B_478)
      | ~ l1_pre_topc(A_477)
      | ~ v2_pre_topc(A_477)
      | v2_struct_0(A_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2671,plain,(
    ! [B_478,E_480] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_478,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_480),u1_struct_0('#skF_4'),u1_struct_0(B_478))
      | ~ v5_pre_topc(E_480,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_478)
      | ~ m1_subset_1(E_480,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_478))))
      | ~ v1_funct_2(E_480,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_478))
      | ~ v1_funct_1(E_480)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_478)
      | ~ v2_pre_topc(B_478)
      | v2_struct_0(B_478)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2669])).

tff(c_2673,plain,(
    ! [B_478,E_480] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_478,'#skF_1','#skF_4',E_480),u1_struct_0('#skF_4'),u1_struct_0(B_478))
      | ~ v5_pre_topc(E_480,'#skF_1',B_478)
      | ~ m1_subset_1(E_480,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_478))))
      | ~ v1_funct_2(E_480,u1_struct_0('#skF_1'),u1_struct_0(B_478))
      | ~ v1_funct_1(E_480)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_478)
      | ~ v2_pre_topc(B_478)
      | v2_struct_0(B_478)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_2537,c_34,c_34,c_34,c_2671])).

tff(c_2675,plain,(
    ! [B_482,E_483] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_482,'#skF_1','#skF_4',E_483),u1_struct_0('#skF_4'),u1_struct_0(B_482))
      | ~ v5_pre_topc(E_483,'#skF_1',B_482)
      | ~ m1_subset_1(E_483,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_482))))
      | ~ v1_funct_2(E_483,u1_struct_0('#skF_1'),u1_struct_0(B_482))
      | ~ v1_funct_1(E_483)
      | ~ l1_pre_topc(B_482)
      | ~ v2_pre_topc(B_482)
      | v2_struct_0(B_482) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_2673])).

tff(c_2677,plain,
    ( v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2675])).

tff(c_2680,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2344,c_2495,c_2677])).

tff(c_2682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2345,c_2680])).

tff(c_2684,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_2683,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_2708,plain,(
    ! [E_493,B_492,C_495,A_496,D_494] :
      ( k3_tmap_1(A_496,B_492,C_495,D_494,E_493) = k2_partfun1(u1_struct_0(C_495),u1_struct_0(B_492),E_493,u1_struct_0(D_494))
      | ~ m1_pre_topc(D_494,C_495)
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_495),u1_struct_0(B_492))))
      | ~ v1_funct_2(E_493,u1_struct_0(C_495),u1_struct_0(B_492))
      | ~ v1_funct_1(E_493)
      | ~ m1_pre_topc(D_494,A_496)
      | ~ m1_pre_topc(C_495,A_496)
      | ~ l1_pre_topc(B_492)
      | ~ v2_pre_topc(B_492)
      | v2_struct_0(B_492)
      | ~ l1_pre_topc(A_496)
      | ~ v2_pre_topc(A_496)
      | v2_struct_0(A_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2710,plain,(
    ! [A_496,D_494] :
      ( k3_tmap_1(A_496,'#skF_2','#skF_1',D_494,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_494))
      | ~ m1_pre_topc(D_494,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_494,A_496)
      | ~ m1_pre_topc('#skF_1',A_496)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_496)
      | ~ v2_pre_topc(A_496)
      | v2_struct_0(A_496) ) ),
    inference(resolution,[status(thm)],[c_48,c_2708])).

tff(c_2713,plain,(
    ! [A_496,D_494] :
      ( k3_tmap_1(A_496,'#skF_2','#skF_1',D_494,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_494))
      | ~ m1_pre_topc(D_494,'#skF_1')
      | ~ m1_pre_topc(D_494,A_496)
      | ~ m1_pre_topc('#skF_1',A_496)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_496)
      | ~ v2_pre_topc(A_496)
      | v2_struct_0(A_496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2710])).

tff(c_2715,plain,(
    ! [A_497,D_498] :
      ( k3_tmap_1(A_497,'#skF_2','#skF_1',D_498,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_498))
      | ~ m1_pre_topc(D_498,'#skF_1')
      | ~ m1_pre_topc(D_498,A_497)
      | ~ m1_pre_topc('#skF_1',A_497)
      | ~ l1_pre_topc(A_497)
      | ~ v2_pre_topc(A_497)
      | v2_struct_0(A_497) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2713])).

tff(c_2719,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2715])).

tff(c_2725,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_36,c_2719])).

tff(c_2726,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2725])).

tff(c_2731,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2726])).

tff(c_2734,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_2731])).

tff(c_2738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2734])).

tff(c_2740,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2726])).

tff(c_2721,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2715])).

tff(c_2729,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_2721])).

tff(c_2730,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2729])).

tff(c_2826,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2740,c_2730])).

tff(c_2690,plain,(
    ! [A_487,B_488,C_489,D_490] :
      ( k2_partfun1(u1_struct_0(A_487),u1_struct_0(B_488),C_489,u1_struct_0(D_490)) = k2_tmap_1(A_487,B_488,C_489,D_490)
      | ~ m1_pre_topc(D_490,A_487)
      | ~ m1_subset_1(C_489,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_487),u1_struct_0(B_488))))
      | ~ v1_funct_2(C_489,u1_struct_0(A_487),u1_struct_0(B_488))
      | ~ v1_funct_1(C_489)
      | ~ l1_pre_topc(B_488)
      | ~ v2_pre_topc(B_488)
      | v2_struct_0(B_488)
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2692,plain,(
    ! [D_490] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_490)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_490)
      | ~ m1_pre_topc(D_490,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_2690])).

tff(c_2695,plain,(
    ! [D_490] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_490)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_490)
      | ~ m1_pre_topc(D_490,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_2692])).

tff(c_2696,plain,(
    ! [D_490] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_490)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_490)
      | ~ m1_pre_topc(D_490,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_2695])).

tff(c_2830,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2826,c_2696])).

tff(c_2837,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2830])).

tff(c_2747,plain,(
    ! [B_500,E_502,D_503,C_501,A_499] :
      ( v1_funct_1(k3_tmap_1(A_499,B_500,k1_tsep_1(A_499,C_501,D_503),D_503,E_502))
      | ~ v5_pre_topc(E_502,k1_tsep_1(A_499,C_501,D_503),B_500)
      | ~ m1_subset_1(E_502,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_499,C_501,D_503)),u1_struct_0(B_500))))
      | ~ v1_funct_2(E_502,u1_struct_0(k1_tsep_1(A_499,C_501,D_503)),u1_struct_0(B_500))
      | ~ v1_funct_1(E_502)
      | ~ r4_tsep_1(A_499,C_501,D_503)
      | ~ m1_pre_topc(D_503,A_499)
      | v2_struct_0(D_503)
      | ~ m1_pre_topc(C_501,A_499)
      | v2_struct_0(C_501)
      | ~ l1_pre_topc(B_500)
      | ~ v2_pre_topc(B_500)
      | v2_struct_0(B_500)
      | ~ l1_pre_topc(A_499)
      | ~ v2_pre_topc(A_499)
      | v2_struct_0(A_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2749,plain,(
    ! [B_500,E_502] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_500,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_502))
      | ~ v5_pre_topc(E_502,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_500)
      | ~ m1_subset_1(E_502,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_500))))
      | ~ v1_funct_2(E_502,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_500))
      | ~ v1_funct_1(E_502)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_500)
      | ~ v2_pre_topc(B_500)
      | v2_struct_0(B_500)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2747])).

tff(c_2751,plain,(
    ! [B_500,E_502] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_500,'#skF_1','#skF_5',E_502))
      | ~ v5_pre_topc(E_502,'#skF_1',B_500)
      | ~ m1_subset_1(E_502,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_500))))
      | ~ v1_funct_2(E_502,u1_struct_0('#skF_1'),u1_struct_0(B_500))
      | ~ v1_funct_1(E_502)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_500)
      | ~ v2_pre_topc(B_500)
      | v2_struct_0(B_500)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_34,c_34,c_34,c_2749])).

tff(c_2752,plain,(
    ! [B_500,E_502] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_500,'#skF_1','#skF_5',E_502))
      | ~ v5_pre_topc(E_502,'#skF_1',B_500)
      | ~ m1_subset_1(E_502,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_500))))
      | ~ v1_funct_2(E_502,u1_struct_0('#skF_1'),u1_struct_0(B_500))
      | ~ v1_funct_1(E_502)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ l1_pre_topc(B_500)
      | ~ v2_pre_topc(B_500)
      | v2_struct_0(B_500) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_2751])).

tff(c_2869,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2752])).

tff(c_2872,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_tsep_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2869])).

tff(c_2875,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_42,c_38,c_36,c_2872])).

tff(c_2877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2875])).

tff(c_2879,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2752])).

tff(c_2998,plain,(
    ! [C_524,E_525,A_522,D_526,B_523] :
      ( v5_pre_topc(k3_tmap_1(A_522,B_523,k1_tsep_1(A_522,C_524,D_526),C_524,E_525),C_524,B_523)
      | ~ v5_pre_topc(E_525,k1_tsep_1(A_522,C_524,D_526),B_523)
      | ~ m1_subset_1(E_525,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_522,C_524,D_526)),u1_struct_0(B_523))))
      | ~ v1_funct_2(E_525,u1_struct_0(k1_tsep_1(A_522,C_524,D_526)),u1_struct_0(B_523))
      | ~ v1_funct_1(E_525)
      | ~ r4_tsep_1(A_522,C_524,D_526)
      | ~ m1_pre_topc(D_526,A_522)
      | v2_struct_0(D_526)
      | ~ m1_pre_topc(C_524,A_522)
      | v2_struct_0(C_524)
      | ~ l1_pre_topc(B_523)
      | ~ v2_pre_topc(B_523)
      | v2_struct_0(B_523)
      | ~ l1_pre_topc(A_522)
      | ~ v2_pre_topc(A_522)
      | v2_struct_0(A_522) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3000,plain,(
    ! [B_523,E_525] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_523,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_525),'#skF_4',B_523)
      | ~ v5_pre_topc(E_525,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_523)
      | ~ m1_subset_1(E_525,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_523))))
      | ~ v1_funct_2(E_525,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_523))
      | ~ v1_funct_1(E_525)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_523)
      | ~ v2_pre_topc(B_523)
      | v2_struct_0(B_523)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2998])).

tff(c_3002,plain,(
    ! [B_523,E_525] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_523,'#skF_1','#skF_4',E_525),'#skF_4',B_523)
      | ~ v5_pre_topc(E_525,'#skF_1',B_523)
      | ~ m1_subset_1(E_525,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_523))))
      | ~ v1_funct_2(E_525,u1_struct_0('#skF_1'),u1_struct_0(B_523))
      | ~ v1_funct_1(E_525)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_523)
      | ~ v2_pre_topc(B_523)
      | v2_struct_0(B_523)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_2879,c_34,c_34,c_34,c_3000])).

tff(c_3004,plain,(
    ! [B_527,E_528] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_527,'#skF_1','#skF_4',E_528),'#skF_4',B_527)
      | ~ v5_pre_topc(E_528,'#skF_1',B_527)
      | ~ m1_subset_1(E_528,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_527))))
      | ~ v1_funct_2(E_528,u1_struct_0('#skF_1'),u1_struct_0(B_527))
      | ~ v1_funct_1(E_528)
      | ~ l1_pre_topc(B_527)
      | ~ v2_pre_topc(B_527)
      | v2_struct_0(B_527) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_3002])).

tff(c_3006,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_3004])).

tff(c_3009,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2683,c_2837,c_3006])).

tff(c_3011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2684,c_3009])).

tff(c_3013,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_3012,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_3036,plain,(
    ! [C_540,D_539,B_537,A_541,E_538] :
      ( k3_tmap_1(A_541,B_537,C_540,D_539,E_538) = k2_partfun1(u1_struct_0(C_540),u1_struct_0(B_537),E_538,u1_struct_0(D_539))
      | ~ m1_pre_topc(D_539,C_540)
      | ~ m1_subset_1(E_538,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_540),u1_struct_0(B_537))))
      | ~ v1_funct_2(E_538,u1_struct_0(C_540),u1_struct_0(B_537))
      | ~ v1_funct_1(E_538)
      | ~ m1_pre_topc(D_539,A_541)
      | ~ m1_pre_topc(C_540,A_541)
      | ~ l1_pre_topc(B_537)
      | ~ v2_pre_topc(B_537)
      | v2_struct_0(B_537)
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541)
      | v2_struct_0(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3038,plain,(
    ! [A_541,D_539] :
      ( k3_tmap_1(A_541,'#skF_2','#skF_1',D_539,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_539))
      | ~ m1_pre_topc(D_539,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_539,A_541)
      | ~ m1_pre_topc('#skF_1',A_541)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541)
      | v2_struct_0(A_541) ) ),
    inference(resolution,[status(thm)],[c_48,c_3036])).

tff(c_3041,plain,(
    ! [A_541,D_539] :
      ( k3_tmap_1(A_541,'#skF_2','#skF_1',D_539,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_539))
      | ~ m1_pre_topc(D_539,'#skF_1')
      | ~ m1_pre_topc(D_539,A_541)
      | ~ m1_pre_topc('#skF_1',A_541)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541)
      | v2_struct_0(A_541) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_3038])).

tff(c_3043,plain,(
    ! [A_542,D_543] :
      ( k3_tmap_1(A_542,'#skF_2','#skF_1',D_543,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_543))
      | ~ m1_pre_topc(D_543,'#skF_1')
      | ~ m1_pre_topc(D_543,A_542)
      | ~ m1_pre_topc('#skF_1',A_542)
      | ~ l1_pre_topc(A_542)
      | ~ v2_pre_topc(A_542)
      | v2_struct_0(A_542) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3041])).

tff(c_3047,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_3043])).

tff(c_3053,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_36,c_3047])).

tff(c_3054,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3053])).

tff(c_3059,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3054])).

tff(c_3062,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3059])).

tff(c_3066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3062])).

tff(c_3067,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3054])).

tff(c_3020,plain,(
    ! [A_532,B_533,C_534,D_535] :
      ( k2_partfun1(u1_struct_0(A_532),u1_struct_0(B_533),C_534,u1_struct_0(D_535)) = k2_tmap_1(A_532,B_533,C_534,D_535)
      | ~ m1_pre_topc(D_535,A_532)
      | ~ m1_subset_1(C_534,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_532),u1_struct_0(B_533))))
      | ~ v1_funct_2(C_534,u1_struct_0(A_532),u1_struct_0(B_533))
      | ~ v1_funct_1(C_534)
      | ~ l1_pre_topc(B_533)
      | ~ v2_pre_topc(B_533)
      | v2_struct_0(B_533)
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532)
      | v2_struct_0(A_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3022,plain,(
    ! [D_535] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_535)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_535)
      | ~ m1_pre_topc(D_535,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_3020])).

tff(c_3025,plain,(
    ! [D_535] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_535)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_535)
      | ~ m1_pre_topc(D_535,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_3022])).

tff(c_3026,plain,(
    ! [D_535] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_535)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_535)
      | ~ m1_pre_topc(D_535,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_3025])).

tff(c_3078,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3067,c_3026])).

tff(c_3085,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3078])).

tff(c_3191,plain,(
    ! [C_551,A_549,E_552,B_550,D_553] :
      ( v1_funct_1(k3_tmap_1(A_549,B_550,k1_tsep_1(A_549,C_551,D_553),D_553,E_552))
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

tff(c_3193,plain,(
    ! [B_550,E_552] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_550,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_552))
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
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3191])).

tff(c_3195,plain,(
    ! [B_550,E_552] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_550,'#skF_1','#skF_5',E_552))
      | ~ v5_pre_topc(E_552,'#skF_1',B_550)
      | ~ m1_subset_1(E_552,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_550))))
      | ~ v1_funct_2(E_552,u1_struct_0('#skF_1'),u1_struct_0(B_550))
      | ~ v1_funct_1(E_552)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_550)
      | ~ v2_pre_topc(B_550)
      | v2_struct_0(B_550)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_34,c_34,c_34,c_3193])).

tff(c_3196,plain,(
    ! [B_550,E_552] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_550,'#skF_1','#skF_5',E_552))
      | ~ v5_pre_topc(E_552,'#skF_1',B_550)
      | ~ m1_subset_1(E_552,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_550))))
      | ~ v1_funct_2(E_552,u1_struct_0('#skF_1'),u1_struct_0(B_550))
      | ~ v1_funct_1(E_552)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ l1_pre_topc(B_550)
      | ~ v2_pre_topc(B_550)
      | v2_struct_0(B_550) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_3195])).

tff(c_3290,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3196])).

tff(c_3293,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_tsep_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3290])).

tff(c_3296,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_42,c_38,c_36,c_3293])).

tff(c_3298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3296])).

tff(c_3300,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_3196])).

tff(c_3284,plain,(
    ! [C_558,B_557,D_560,A_556,E_559] :
      ( v5_pre_topc(k3_tmap_1(A_556,B_557,k1_tsep_1(A_556,C_558,D_560),D_560,E_559),D_560,B_557)
      | ~ v5_pre_topc(E_559,k1_tsep_1(A_556,C_558,D_560),B_557)
      | ~ m1_subset_1(E_559,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_556,C_558,D_560)),u1_struct_0(B_557))))
      | ~ v1_funct_2(E_559,u1_struct_0(k1_tsep_1(A_556,C_558,D_560)),u1_struct_0(B_557))
      | ~ v1_funct_1(E_559)
      | ~ r4_tsep_1(A_556,C_558,D_560)
      | ~ m1_pre_topc(D_560,A_556)
      | v2_struct_0(D_560)
      | ~ m1_pre_topc(C_558,A_556)
      | v2_struct_0(C_558)
      | ~ l1_pre_topc(B_557)
      | ~ v2_pre_topc(B_557)
      | v2_struct_0(B_557)
      | ~ l1_pre_topc(A_556)
      | ~ v2_pre_topc(A_556)
      | v2_struct_0(A_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3286,plain,(
    ! [B_557,E_559] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_557,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_559),'#skF_5',B_557)
      | ~ v5_pre_topc(E_559,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_557)
      | ~ m1_subset_1(E_559,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_557))))
      | ~ v1_funct_2(E_559,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_557))
      | ~ v1_funct_1(E_559)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_557)
      | ~ v2_pre_topc(B_557)
      | v2_struct_0(B_557)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3284])).

tff(c_3288,plain,(
    ! [B_557,E_559] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_557,'#skF_1','#skF_5',E_559),'#skF_5',B_557)
      | ~ v5_pre_topc(E_559,'#skF_1',B_557)
      | ~ m1_subset_1(E_559,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_557))))
      | ~ v1_funct_2(E_559,u1_struct_0('#skF_1'),u1_struct_0(B_557))
      | ~ v1_funct_1(E_559)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_557)
      | ~ v2_pre_topc(B_557)
      | v2_struct_0(B_557)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_34,c_34,c_34,c_3286])).

tff(c_3289,plain,(
    ! [B_557,E_559] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_557,'#skF_1','#skF_5',E_559),'#skF_5',B_557)
      | ~ v5_pre_topc(E_559,'#skF_1',B_557)
      | ~ m1_subset_1(E_559,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_557))))
      | ~ v1_funct_2(E_559,u1_struct_0('#skF_1'),u1_struct_0(B_557))
      | ~ v1_funct_1(E_559)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ l1_pre_topc(B_557)
      | ~ v2_pre_topc(B_557)
      | v2_struct_0(B_557) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_3288])).

tff(c_3321,plain,(
    ! [B_565,E_566] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_565,'#skF_1','#skF_5',E_566),'#skF_5',B_565)
      | ~ v5_pre_topc(E_566,'#skF_1',B_565)
      | ~ m1_subset_1(E_566,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_565))))
      | ~ v1_funct_2(E_566,u1_struct_0('#skF_1'),u1_struct_0(B_565))
      | ~ v1_funct_1(E_566)
      | ~ l1_pre_topc(B_565)
      | ~ v2_pre_topc(B_565)
      | v2_struct_0(B_565) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3300,c_3289])).

tff(c_3323,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'),'#skF_5','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_3321])).

tff(c_3326,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_3012,c_3085,c_3323])).

tff(c_3328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3013,c_3326])).

tff(c_3330,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_3329,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_3354,plain,(
    ! [E_576,A_579,B_575,C_578,D_577] :
      ( k3_tmap_1(A_579,B_575,C_578,D_577,E_576) = k2_partfun1(u1_struct_0(C_578),u1_struct_0(B_575),E_576,u1_struct_0(D_577))
      | ~ m1_pre_topc(D_577,C_578)
      | ~ m1_subset_1(E_576,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_578),u1_struct_0(B_575))))
      | ~ v1_funct_2(E_576,u1_struct_0(C_578),u1_struct_0(B_575))
      | ~ v1_funct_1(E_576)
      | ~ m1_pre_topc(D_577,A_579)
      | ~ m1_pre_topc(C_578,A_579)
      | ~ l1_pre_topc(B_575)
      | ~ v2_pre_topc(B_575)
      | v2_struct_0(B_575)
      | ~ l1_pre_topc(A_579)
      | ~ v2_pre_topc(A_579)
      | v2_struct_0(A_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3356,plain,(
    ! [A_579,D_577] :
      ( k3_tmap_1(A_579,'#skF_2','#skF_1',D_577,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_577))
      | ~ m1_pre_topc(D_577,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_577,A_579)
      | ~ m1_pre_topc('#skF_1',A_579)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_579)
      | ~ v2_pre_topc(A_579)
      | v2_struct_0(A_579) ) ),
    inference(resolution,[status(thm)],[c_48,c_3354])).

tff(c_3359,plain,(
    ! [A_579,D_577] :
      ( k3_tmap_1(A_579,'#skF_2','#skF_1',D_577,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_577))
      | ~ m1_pre_topc(D_577,'#skF_1')
      | ~ m1_pre_topc(D_577,A_579)
      | ~ m1_pre_topc('#skF_1',A_579)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_579)
      | ~ v2_pre_topc(A_579)
      | v2_struct_0(A_579) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_3356])).

tff(c_3361,plain,(
    ! [A_580,D_581] :
      ( k3_tmap_1(A_580,'#skF_2','#skF_1',D_581,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_581))
      | ~ m1_pre_topc(D_581,'#skF_1')
      | ~ m1_pre_topc(D_581,A_580)
      | ~ m1_pre_topc('#skF_1',A_580)
      | ~ l1_pre_topc(A_580)
      | ~ v2_pre_topc(A_580)
      | v2_struct_0(A_580) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3359])).

tff(c_3365,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_3361])).

tff(c_3371,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_36,c_3365])).

tff(c_3372,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3371])).

tff(c_3383,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3372])).

tff(c_3386,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3383])).

tff(c_3390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3386])).

tff(c_3391,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3372])).

tff(c_3338,plain,(
    ! [A_570,B_571,C_572,D_573] :
      ( k2_partfun1(u1_struct_0(A_570),u1_struct_0(B_571),C_572,u1_struct_0(D_573)) = k2_tmap_1(A_570,B_571,C_572,D_573)
      | ~ m1_pre_topc(D_573,A_570)
      | ~ m1_subset_1(C_572,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_570),u1_struct_0(B_571))))
      | ~ v1_funct_2(C_572,u1_struct_0(A_570),u1_struct_0(B_571))
      | ~ v1_funct_1(C_572)
      | ~ l1_pre_topc(B_571)
      | ~ v2_pre_topc(B_571)
      | v2_struct_0(B_571)
      | ~ l1_pre_topc(A_570)
      | ~ v2_pre_topc(A_570)
      | v2_struct_0(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3340,plain,(
    ! [D_573] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_573)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_573)
      | ~ m1_pre_topc(D_573,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_3338])).

tff(c_3343,plain,(
    ! [D_573] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_573)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_573)
      | ~ m1_pre_topc(D_573,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_3340])).

tff(c_3344,plain,(
    ! [D_573] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_573)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_573)
      | ~ m1_pre_topc(D_573,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_3343])).

tff(c_3438,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3391,c_3344])).

tff(c_3445,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3438])).

tff(c_3377,plain,(
    ! [C_584,D_586,E_585,A_582,B_583] :
      ( v1_funct_1(k3_tmap_1(A_582,B_583,k1_tsep_1(A_582,C_584,D_586),D_586,E_585))
      | ~ v5_pre_topc(E_585,k1_tsep_1(A_582,C_584,D_586),B_583)
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_582,C_584,D_586)),u1_struct_0(B_583))))
      | ~ v1_funct_2(E_585,u1_struct_0(k1_tsep_1(A_582,C_584,D_586)),u1_struct_0(B_583))
      | ~ v1_funct_1(E_585)
      | ~ r4_tsep_1(A_582,C_584,D_586)
      | ~ m1_pre_topc(D_586,A_582)
      | v2_struct_0(D_586)
      | ~ m1_pre_topc(C_584,A_582)
      | v2_struct_0(C_584)
      | ~ l1_pre_topc(B_583)
      | ~ v2_pre_topc(B_583)
      | v2_struct_0(B_583)
      | ~ l1_pre_topc(A_582)
      | ~ v2_pre_topc(A_582)
      | v2_struct_0(A_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3379,plain,(
    ! [B_583,E_585] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_583,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_585))
      | ~ v5_pre_topc(E_585,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_583)
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_583))))
      | ~ v1_funct_2(E_585,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_583))
      | ~ v1_funct_1(E_585)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_583)
      | ~ v2_pre_topc(B_583)
      | v2_struct_0(B_583)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3377])).

tff(c_3381,plain,(
    ! [B_583,E_585] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_583,'#skF_1','#skF_5',E_585))
      | ~ v5_pre_topc(E_585,'#skF_1',B_583)
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_583))))
      | ~ v1_funct_2(E_585,u1_struct_0('#skF_1'),u1_struct_0(B_583))
      | ~ v1_funct_1(E_585)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_583)
      | ~ v2_pre_topc(B_583)
      | v2_struct_0(B_583)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_34,c_34,c_34,c_3379])).

tff(c_3382,plain,(
    ! [B_583,E_585] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_583,'#skF_1','#skF_5',E_585))
      | ~ v5_pre_topc(E_585,'#skF_1',B_583)
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_583))))
      | ~ v1_funct_2(E_585,u1_struct_0('#skF_1'),u1_struct_0(B_583))
      | ~ v1_funct_1(E_585)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ l1_pre_topc(B_583)
      | ~ v2_pre_topc(B_583)
      | v2_struct_0(B_583) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_3381])).

tff(c_3493,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3382])).

tff(c_3496,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_tsep_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3493])).

tff(c_3499,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_42,c_38,c_36,c_3496])).

tff(c_3501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3499])).

tff(c_3625,plain,(
    ! [B_604,E_605] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_604,'#skF_1','#skF_5',E_605))
      | ~ v5_pre_topc(E_605,'#skF_1',B_604)
      | ~ m1_subset_1(E_605,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_604))))
      | ~ v1_funct_2(E_605,u1_struct_0('#skF_1'),u1_struct_0(B_604))
      | ~ v1_funct_1(E_605)
      | ~ l1_pre_topc(B_604)
      | ~ v2_pre_topc(B_604)
      | v2_struct_0(B_604) ) ),
    inference(splitRight,[status(thm)],[c_3382])).

tff(c_3628,plain,
    ( v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_3625])).

tff(c_3631,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_3329,c_3445,c_3628])).

tff(c_3633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3330,c_3631])).

tff(c_3635,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_3634,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_3662,plain,(
    ! [E_615,D_616,C_617,A_618,B_614] :
      ( k3_tmap_1(A_618,B_614,C_617,D_616,E_615) = k2_partfun1(u1_struct_0(C_617),u1_struct_0(B_614),E_615,u1_struct_0(D_616))
      | ~ m1_pre_topc(D_616,C_617)
      | ~ m1_subset_1(E_615,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_617),u1_struct_0(B_614))))
      | ~ v1_funct_2(E_615,u1_struct_0(C_617),u1_struct_0(B_614))
      | ~ v1_funct_1(E_615)
      | ~ m1_pre_topc(D_616,A_618)
      | ~ m1_pre_topc(C_617,A_618)
      | ~ l1_pre_topc(B_614)
      | ~ v2_pre_topc(B_614)
      | v2_struct_0(B_614)
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3664,plain,(
    ! [A_618,D_616] :
      ( k3_tmap_1(A_618,'#skF_2','#skF_1',D_616,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_616))
      | ~ m1_pre_topc(D_616,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_616,A_618)
      | ~ m1_pre_topc('#skF_1',A_618)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(resolution,[status(thm)],[c_48,c_3662])).

tff(c_3667,plain,(
    ! [A_618,D_616] :
      ( k3_tmap_1(A_618,'#skF_2','#skF_1',D_616,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_616))
      | ~ m1_pre_topc(D_616,'#skF_1')
      | ~ m1_pre_topc(D_616,A_618)
      | ~ m1_pre_topc('#skF_1',A_618)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_3664])).

tff(c_3669,plain,(
    ! [A_619,D_620] :
      ( k3_tmap_1(A_619,'#skF_2','#skF_1',D_620,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_620))
      | ~ m1_pre_topc(D_620,'#skF_1')
      | ~ m1_pre_topc(D_620,A_619)
      | ~ m1_pre_topc('#skF_1',A_619)
      | ~ l1_pre_topc(A_619)
      | ~ v2_pre_topc(A_619)
      | v2_struct_0(A_619) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3667])).

tff(c_3673,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_3669])).

tff(c_3679,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_36,c_3673])).

tff(c_3680,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3679])).

tff(c_3685,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3680])).

tff(c_3688,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_3685])).

tff(c_3692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3688])).

tff(c_3694,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_3680])).

tff(c_3675,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_3669])).

tff(c_3683,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_3675])).

tff(c_3684,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3683])).

tff(c_3780,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3694,c_3684])).

tff(c_3644,plain,(
    ! [A_609,B_610,C_611,D_612] :
      ( k2_partfun1(u1_struct_0(A_609),u1_struct_0(B_610),C_611,u1_struct_0(D_612)) = k2_tmap_1(A_609,B_610,C_611,D_612)
      | ~ m1_pre_topc(D_612,A_609)
      | ~ m1_subset_1(C_611,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_609),u1_struct_0(B_610))))
      | ~ v1_funct_2(C_611,u1_struct_0(A_609),u1_struct_0(B_610))
      | ~ v1_funct_1(C_611)
      | ~ l1_pre_topc(B_610)
      | ~ v2_pre_topc(B_610)
      | v2_struct_0(B_610)
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3646,plain,(
    ! [D_612] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_612)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_612)
      | ~ m1_pre_topc(D_612,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_3644])).

tff(c_3649,plain,(
    ! [D_612] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_612)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_612)
      | ~ m1_pre_topc(D_612,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_3646])).

tff(c_3650,plain,(
    ! [D_612] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_612)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_612)
      | ~ m1_pre_topc(D_612,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_3649])).

tff(c_3784,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3780,c_3650])).

tff(c_3791,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3784])).

tff(c_3701,plain,(
    ! [C_623,A_621,B_622,E_624,D_625] :
      ( v1_funct_1(k3_tmap_1(A_621,B_622,k1_tsep_1(A_621,C_623,D_625),C_623,E_624))
      | ~ v5_pre_topc(E_624,k1_tsep_1(A_621,C_623,D_625),B_622)
      | ~ m1_subset_1(E_624,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_621,C_623,D_625)),u1_struct_0(B_622))))
      | ~ v1_funct_2(E_624,u1_struct_0(k1_tsep_1(A_621,C_623,D_625)),u1_struct_0(B_622))
      | ~ v1_funct_1(E_624)
      | ~ r4_tsep_1(A_621,C_623,D_625)
      | ~ m1_pre_topc(D_625,A_621)
      | v2_struct_0(D_625)
      | ~ m1_pre_topc(C_623,A_621)
      | v2_struct_0(C_623)
      | ~ l1_pre_topc(B_622)
      | ~ v2_pre_topc(B_622)
      | v2_struct_0(B_622)
      | ~ l1_pre_topc(A_621)
      | ~ v2_pre_topc(A_621)
      | v2_struct_0(A_621) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3703,plain,(
    ! [B_622,E_624] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_622,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_624))
      | ~ v5_pre_topc(E_624,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_622)
      | ~ m1_subset_1(E_624,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_622))))
      | ~ v1_funct_2(E_624,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_622))
      | ~ v1_funct_1(E_624)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_622)
      | ~ v2_pre_topc(B_622)
      | v2_struct_0(B_622)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3701])).

tff(c_3705,plain,(
    ! [B_622,E_624] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_622,'#skF_1','#skF_4',E_624))
      | ~ v5_pre_topc(E_624,'#skF_1',B_622)
      | ~ m1_subset_1(E_624,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_622))))
      | ~ v1_funct_2(E_624,u1_struct_0('#skF_1'),u1_struct_0(B_622))
      | ~ v1_funct_1(E_624)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_622)
      | ~ v2_pre_topc(B_622)
      | v2_struct_0(B_622)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_42,c_36,c_34,c_34,c_34,c_3703])).

tff(c_3706,plain,(
    ! [B_622,E_624] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_622,'#skF_1','#skF_4',E_624))
      | ~ v5_pre_topc(E_624,'#skF_1',B_622)
      | ~ m1_subset_1(E_624,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_622))))
      | ~ v1_funct_2(E_624,u1_struct_0('#skF_1'),u1_struct_0(B_622))
      | ~ v1_funct_1(E_624)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ l1_pre_topc(B_622)
      | ~ v2_pre_topc(B_622)
      | v2_struct_0(B_622) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_40,c_3705])).

tff(c_3823,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3706])).

tff(c_3826,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_tsep_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3823])).

tff(c_3829,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_42,c_38,c_36,c_3826])).

tff(c_3831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3829])).

tff(c_3927,plain,(
    ! [B_638,E_639] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_638,'#skF_1','#skF_4',E_639))
      | ~ v5_pre_topc(E_639,'#skF_1',B_638)
      | ~ m1_subset_1(E_639,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_638))))
      | ~ v1_funct_2(E_639,u1_struct_0('#skF_1'),u1_struct_0(B_638))
      | ~ v1_funct_1(E_639)
      | ~ l1_pre_topc(B_638)
      | ~ v2_pre_topc(B_638)
      | v2_struct_0(B_638) ) ),
    inference(splitRight,[status(thm)],[c_3706])).

tff(c_3930,plain,
    ( v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_3927])).

tff(c_3933,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_3634,c_3791,c_3930])).

tff(c_3935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3635,c_3933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.27/2.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.55  
% 7.58/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.56  %$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.58/2.56  
% 7.58/2.56  %Foreground sorts:
% 7.58/2.56  
% 7.58/2.56  
% 7.58/2.56  %Background operators:
% 7.58/2.56  
% 7.58/2.56  
% 7.58/2.56  %Foreground operators:
% 7.58/2.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.58/2.56  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 7.58/2.56  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.58/2.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.58/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.58/2.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.58/2.56  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 7.58/2.56  tff('#skF_5', type, '#skF_5': $i).
% 7.58/2.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.58/2.56  tff('#skF_2', type, '#skF_2': $i).
% 7.58/2.56  tff('#skF_3', type, '#skF_3': $i).
% 7.58/2.56  tff('#skF_1', type, '#skF_1': $i).
% 7.58/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.58/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.58/2.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.58/2.56  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 7.58/2.56  tff('#skF_4', type, '#skF_4': $i).
% 7.58/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.58/2.56  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.58/2.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.58/2.56  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.58/2.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.58/2.56  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.58/2.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.58/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.58/2.56  
% 7.89/2.64  tff(f_232, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, A)) & m1_pre_topc(D, A)) => (![E]: (((~v2_struct_0(E) & v1_tsep_1(E, A)) & m1_pre_topc(E, A)) => ((A = k1_tsep_1(A, D, E)) => ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, C, E))) & v1_funct_2(k2_tmap_1(A, B, C, E), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, E), E, B)) & m1_subset_1(k2_tmap_1(A, B, C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_tmap_1)).
% 7.89/2.64  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.89/2.64  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 7.89/2.64  tff(f_52, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.89/2.64  tff(f_167, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((v1_tsep_1(C, A) & m1_pre_topc(C, A)) => r4_tsep_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tsep_1)).
% 7.89/2.64  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_tmap_1)).
% 7.89/2.64  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_150, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_190, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_150])).
% 7.89/2.64  tff(c_140, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_194, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_140])).
% 7.89/2.64  tff(c_130, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_193, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_130])).
% 7.89/2.64  tff(c_120, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_197, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_120])).
% 7.89/2.64  tff(c_110, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_191, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_110])).
% 7.89/2.64  tff(c_100, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_195, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_100])).
% 7.89/2.64  tff(c_90, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_192, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_90])).
% 7.89/2.64  tff(c_80, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_196, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_80])).
% 7.89/2.64  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_66, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_164, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_66])).
% 7.89/2.64  tff(c_174, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_164])).
% 7.89/2.64  tff(c_184, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_174])).
% 7.89/2.64  tff(c_660, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_194, c_193, c_197, c_191, c_195, c_192, c_196, c_184])).
% 7.89/2.64  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_30, plain, (![A_78]: (m1_pre_topc(A_78, A_78) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.89/2.64  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_36, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_218, plain, (![E_121, A_124, D_122, B_120, C_123]: (k3_tmap_1(A_124, B_120, C_123, D_122, E_121)=k2_partfun1(u1_struct_0(C_123), u1_struct_0(B_120), E_121, u1_struct_0(D_122)) | ~m1_pre_topc(D_122, C_123) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_123), u1_struct_0(B_120)))) | ~v1_funct_2(E_121, u1_struct_0(C_123), u1_struct_0(B_120)) | ~v1_funct_1(E_121) | ~m1_pre_topc(D_122, A_124) | ~m1_pre_topc(C_123, A_124) | ~l1_pre_topc(B_120) | ~v2_pre_topc(B_120) | v2_struct_0(B_120) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.89/2.64  tff(c_224, plain, (![A_124, D_122]: (k3_tmap_1(A_124, '#skF_2', '#skF_1', D_122, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_122)) | ~m1_pre_topc(D_122, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_122, A_124) | ~m1_pre_topc('#skF_1', A_124) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124))), inference(resolution, [status(thm)], [c_48, c_218])).
% 7.89/2.64  tff(c_235, plain, (![A_124, D_122]: (k3_tmap_1(A_124, '#skF_2', '#skF_1', D_122, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_122)) | ~m1_pre_topc(D_122, '#skF_1') | ~m1_pre_topc(D_122, A_124) | ~m1_pre_topc('#skF_1', A_124) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_224])).
% 7.89/2.64  tff(c_248, plain, (![A_126, D_127]: (k3_tmap_1(A_126, '#skF_2', '#skF_1', D_127, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_127)) | ~m1_pre_topc(D_127, '#skF_1') | ~m1_pre_topc(D_127, A_126) | ~m1_pre_topc('#skF_1', A_126) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(negUnitSimplification, [status(thm)], [c_58, c_235])).
% 7.89/2.64  tff(c_252, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_248])).
% 7.89/2.64  tff(c_258, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_36, c_252])).
% 7.89/2.64  tff(c_259, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_258])).
% 7.89/2.64  tff(c_264, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_259])).
% 7.89/2.64  tff(c_267, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_264])).
% 7.89/2.64  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_267])).
% 7.89/2.64  tff(c_273, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_259])).
% 7.89/2.64  tff(c_254, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_248])).
% 7.89/2.64  tff(c_262, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_254])).
% 7.89/2.64  tff(c_263, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_262])).
% 7.89/2.64  tff(c_359, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_263])).
% 7.89/2.64  tff(c_199, plain, (![A_116, B_117, C_118, D_119]: (k2_partfun1(u1_struct_0(A_116), u1_struct_0(B_117), C_118, u1_struct_0(D_119))=k2_tmap_1(A_116, B_117, C_118, D_119) | ~m1_pre_topc(D_119, A_116) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116), u1_struct_0(B_117)))) | ~v1_funct_2(C_118, u1_struct_0(A_116), u1_struct_0(B_117)) | ~v1_funct_1(C_118) | ~l1_pre_topc(B_117) | ~v2_pre_topc(B_117) | v2_struct_0(B_117) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.89/2.64  tff(c_205, plain, (![D_119]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_119))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_119) | ~m1_pre_topc(D_119, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_199])).
% 7.89/2.64  tff(c_216, plain, (![D_119]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_119))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_119) | ~m1_pre_topc(D_119, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_205])).
% 7.89/2.64  tff(c_217, plain, (![D_119]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_119))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_119) | ~m1_pre_topc(D_119, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_216])).
% 7.89/2.64  tff(c_363, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_359, c_217])).
% 7.89/2.64  tff(c_370, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_363])).
% 7.89/2.64  tff(c_272, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_259])).
% 7.89/2.64  tff(c_289, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_272, c_217])).
% 7.89/2.64  tff(c_296, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_289])).
% 7.89/2.64  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_40, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_44, plain, (v1_tsep_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_38, plain, (v1_tsep_1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_32, plain, (![A_79, B_83, C_85]: (r4_tsep_1(A_79, B_83, C_85) | ~m1_pre_topc(C_85, A_79) | ~v1_tsep_1(C_85, A_79) | ~m1_pre_topc(B_83, A_79) | ~v1_tsep_1(B_83, A_79) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.89/2.64  tff(c_34, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.89/2.64  tff(c_280, plain, (![B_129, C_130, A_128, D_132, E_131]: (v1_funct_1(k3_tmap_1(A_128, B_129, k1_tsep_1(A_128, C_130, D_132), D_132, E_131)) | ~v5_pre_topc(E_131, k1_tsep_1(A_128, C_130, D_132), B_129) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_128, C_130, D_132)), u1_struct_0(B_129)))) | ~v1_funct_2(E_131, u1_struct_0(k1_tsep_1(A_128, C_130, D_132)), u1_struct_0(B_129)) | ~v1_funct_1(E_131) | ~r4_tsep_1(A_128, C_130, D_132) | ~m1_pre_topc(D_132, A_128) | v2_struct_0(D_132) | ~m1_pre_topc(C_130, A_128) | v2_struct_0(C_130) | ~l1_pre_topc(B_129) | ~v2_pre_topc(B_129) | v2_struct_0(B_129) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_282, plain, (![B_129, E_131]: (v1_funct_1(k3_tmap_1('#skF_1', B_129, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_131)) | ~v5_pre_topc(E_131, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_129) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_129)))) | ~v1_funct_2(E_131, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_129)) | ~v1_funct_1(E_131) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_129) | ~v2_pre_topc(B_129) | v2_struct_0(B_129) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_280])).
% 7.89/2.64  tff(c_284, plain, (![B_129, E_131]: (v1_funct_1(k3_tmap_1('#skF_1', B_129, '#skF_1', '#skF_5', E_131)) | ~v5_pre_topc(E_131, '#skF_1', B_129) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_129)))) | ~v1_funct_2(E_131, u1_struct_0('#skF_1'), u1_struct_0(B_129)) | ~v1_funct_1(E_131) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_129) | ~v2_pre_topc(B_129) | v2_struct_0(B_129) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_34, c_34, c_34, c_282])).
% 7.89/2.64  tff(c_285, plain, (![B_129, E_131]: (v1_funct_1(k3_tmap_1('#skF_1', B_129, '#skF_1', '#skF_5', E_131)) | ~v5_pre_topc(E_131, '#skF_1', B_129) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_129)))) | ~v1_funct_2(E_131, u1_struct_0('#skF_1'), u1_struct_0(B_129)) | ~v1_funct_1(E_131) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~l1_pre_topc(B_129) | ~v2_pre_topc(B_129) | v2_struct_0(B_129))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_284])).
% 7.89/2.64  tff(c_402, plain, (~r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_285])).
% 7.89/2.64  tff(c_405, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~v1_tsep_1('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_402])).
% 7.89/2.64  tff(c_408, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_42, c_38, c_36, c_405])).
% 7.89/2.64  tff(c_410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_408])).
% 7.89/2.64  tff(c_412, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_285])).
% 7.89/2.64  tff(c_838, plain, (![E_197, C_196, A_194, D_198, B_195]: (v5_pre_topc(E_197, k1_tsep_1(A_194, C_196, D_198), B_195) | ~m1_subset_1(k3_tmap_1(A_194, B_195, k1_tsep_1(A_194, C_196, D_198), D_198, E_197), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_198), u1_struct_0(B_195)))) | ~v5_pre_topc(k3_tmap_1(A_194, B_195, k1_tsep_1(A_194, C_196, D_198), D_198, E_197), D_198, B_195) | ~v1_funct_2(k3_tmap_1(A_194, B_195, k1_tsep_1(A_194, C_196, D_198), D_198, E_197), u1_struct_0(D_198), u1_struct_0(B_195)) | ~v1_funct_1(k3_tmap_1(A_194, B_195, k1_tsep_1(A_194, C_196, D_198), D_198, E_197)) | ~m1_subset_1(k3_tmap_1(A_194, B_195, k1_tsep_1(A_194, C_196, D_198), C_196, E_197), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_196), u1_struct_0(B_195)))) | ~v5_pre_topc(k3_tmap_1(A_194, B_195, k1_tsep_1(A_194, C_196, D_198), C_196, E_197), C_196, B_195) | ~v1_funct_2(k3_tmap_1(A_194, B_195, k1_tsep_1(A_194, C_196, D_198), C_196, E_197), u1_struct_0(C_196), u1_struct_0(B_195)) | ~v1_funct_1(k3_tmap_1(A_194, B_195, k1_tsep_1(A_194, C_196, D_198), C_196, E_197)) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_194, C_196, D_198)), u1_struct_0(B_195)))) | ~v1_funct_2(E_197, u1_struct_0(k1_tsep_1(A_194, C_196, D_198)), u1_struct_0(B_195)) | ~v1_funct_1(E_197) | ~r4_tsep_1(A_194, C_196, D_198) | ~m1_pre_topc(D_198, A_194) | v2_struct_0(D_198) | ~m1_pre_topc(C_196, A_194) | v2_struct_0(C_196) | ~l1_pre_topc(B_195) | ~v2_pre_topc(B_195) | v2_struct_0(B_195) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_845, plain, (![E_197, B_195]: (v5_pre_topc(E_197, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_195) | ~m1_subset_1(k3_tmap_1('#skF_1', B_195, '#skF_1', '#skF_5', E_197), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_195)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_195, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_197), '#skF_5', B_195) | ~v1_funct_2(k3_tmap_1('#skF_1', B_195, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_197), u1_struct_0('#skF_5'), u1_struct_0(B_195)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_195, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_197)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_195, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_197), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_195)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_195, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_197), '#skF_4', B_195) | ~v1_funct_2(k3_tmap_1('#skF_1', B_195, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_197), u1_struct_0('#skF_4'), u1_struct_0(B_195)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_195, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_197)) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_195)))) | ~v1_funct_2(E_197, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_195)) | ~v1_funct_1(E_197) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_195) | ~v2_pre_topc(B_195) | v2_struct_0(B_195) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_838])).
% 7.89/2.64  tff(c_849, plain, (![E_197, B_195]: (v5_pre_topc(E_197, '#skF_1', B_195) | ~m1_subset_1(k3_tmap_1('#skF_1', B_195, '#skF_1', '#skF_5', E_197), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_195)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_195, '#skF_1', '#skF_5', E_197), '#skF_5', B_195) | ~v1_funct_2(k3_tmap_1('#skF_1', B_195, '#skF_1', '#skF_5', E_197), u1_struct_0('#skF_5'), u1_struct_0(B_195)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_195, '#skF_1', '#skF_5', E_197)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_195, '#skF_1', '#skF_4', E_197), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_195)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_195, '#skF_1', '#skF_4', E_197), '#skF_4', B_195) | ~v1_funct_2(k3_tmap_1('#skF_1', B_195, '#skF_1', '#skF_4', E_197), u1_struct_0('#skF_4'), u1_struct_0(B_195)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_195, '#skF_1', '#skF_4', E_197)) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_195)))) | ~v1_funct_2(E_197, u1_struct_0('#skF_1'), u1_struct_0(B_195)) | ~v1_funct_1(E_197) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_195) | ~v2_pre_topc(B_195) | v2_struct_0(B_195) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_412, c_34, c_34, c_34, c_34, c_34, c_34, c_34, c_34, c_34, c_34, c_845])).
% 7.89/2.64  tff(c_907, plain, (![E_225, B_226]: (v5_pre_topc(E_225, '#skF_1', B_226) | ~m1_subset_1(k3_tmap_1('#skF_1', B_226, '#skF_1', '#skF_5', E_225), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_226)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_226, '#skF_1', '#skF_5', E_225), '#skF_5', B_226) | ~v1_funct_2(k3_tmap_1('#skF_1', B_226, '#skF_1', '#skF_5', E_225), u1_struct_0('#skF_5'), u1_struct_0(B_226)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_226, '#skF_1', '#skF_5', E_225)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_226, '#skF_1', '#skF_4', E_225), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_226)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_226, '#skF_1', '#skF_4', E_225), '#skF_4', B_226) | ~v1_funct_2(k3_tmap_1('#skF_1', B_226, '#skF_1', '#skF_4', E_225), u1_struct_0('#skF_4'), u1_struct_0(B_226)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_226, '#skF_1', '#skF_4', E_225)) | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_226)))) | ~v1_funct_2(E_225, u1_struct_0('#skF_1'), u1_struct_0(B_226)) | ~v1_funct_1(E_225) | ~l1_pre_topc(B_226) | ~v2_pre_topc(B_226) | v2_struct_0(B_226))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_849])).
% 7.89/2.64  tff(c_913, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), '#skF_5', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_296, c_907])).
% 7.89/2.64  tff(c_916, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_190, c_370, c_194, c_370, c_193, c_370, c_197, c_370, c_191, c_296, c_195, c_296, c_192, c_296, c_196, c_913])).
% 7.89/2.64  tff(c_918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_660, c_916])).
% 7.89/2.64  tff(c_920, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_120])).
% 7.89/2.64  tff(c_919, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_120])).
% 7.89/2.64  tff(c_945, plain, (![C_238, A_239, D_237, E_236, B_235]: (k3_tmap_1(A_239, B_235, C_238, D_237, E_236)=k2_partfun1(u1_struct_0(C_238), u1_struct_0(B_235), E_236, u1_struct_0(D_237)) | ~m1_pre_topc(D_237, C_238) | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_238), u1_struct_0(B_235)))) | ~v1_funct_2(E_236, u1_struct_0(C_238), u1_struct_0(B_235)) | ~v1_funct_1(E_236) | ~m1_pre_topc(D_237, A_239) | ~m1_pre_topc(C_238, A_239) | ~l1_pre_topc(B_235) | ~v2_pre_topc(B_235) | v2_struct_0(B_235) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239) | v2_struct_0(A_239))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.89/2.64  tff(c_949, plain, (![A_239, D_237]: (k3_tmap_1(A_239, '#skF_2', '#skF_1', D_237, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_237)) | ~m1_pre_topc(D_237, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_237, A_239) | ~m1_pre_topc('#skF_1', A_239) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239) | v2_struct_0(A_239))), inference(resolution, [status(thm)], [c_48, c_945])).
% 7.89/2.64  tff(c_956, plain, (![A_239, D_237]: (k3_tmap_1(A_239, '#skF_2', '#skF_1', D_237, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_237)) | ~m1_pre_topc(D_237, '#skF_1') | ~m1_pre_topc(D_237, A_239) | ~m1_pre_topc('#skF_1', A_239) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239) | v2_struct_0(A_239))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_949])).
% 7.89/2.64  tff(c_958, plain, (![A_240, D_241]: (k3_tmap_1(A_240, '#skF_2', '#skF_1', D_241, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_241)) | ~m1_pre_topc(D_241, '#skF_1') | ~m1_pre_topc(D_241, A_240) | ~m1_pre_topc('#skF_1', A_240) | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(negUnitSimplification, [status(thm)], [c_58, c_956])).
% 7.89/2.64  tff(c_962, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_958])).
% 7.89/2.64  tff(c_968, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_36, c_962])).
% 7.89/2.64  tff(c_969, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_968])).
% 7.89/2.64  tff(c_974, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_969])).
% 7.89/2.64  tff(c_977, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_974])).
% 7.89/2.64  tff(c_981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_977])).
% 7.89/2.64  tff(c_983, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_969])).
% 7.89/2.64  tff(c_964, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_958])).
% 7.89/2.64  tff(c_972, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_964])).
% 7.89/2.64  tff(c_973, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_972])).
% 7.89/2.64  tff(c_1075, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_983, c_973])).
% 7.89/2.64  tff(c_922, plain, (![A_230, B_231, C_232, D_233]: (k2_partfun1(u1_struct_0(A_230), u1_struct_0(B_231), C_232, u1_struct_0(D_233))=k2_tmap_1(A_230, B_231, C_232, D_233) | ~m1_pre_topc(D_233, A_230) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_230), u1_struct_0(B_231)))) | ~v1_funct_2(C_232, u1_struct_0(A_230), u1_struct_0(B_231)) | ~v1_funct_1(C_232) | ~l1_pre_topc(B_231) | ~v2_pre_topc(B_231) | v2_struct_0(B_231) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.89/2.64  tff(c_926, plain, (![D_233]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_233))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_233) | ~m1_pre_topc(D_233, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_922])).
% 7.89/2.64  tff(c_933, plain, (![D_233]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_233))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_233) | ~m1_pre_topc(D_233, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_926])).
% 7.89/2.64  tff(c_934, plain, (![D_233]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_233))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_233) | ~m1_pre_topc(D_233, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_933])).
% 7.89/2.64  tff(c_1079, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1075, c_934])).
% 7.89/2.64  tff(c_1086, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1079])).
% 7.89/2.64  tff(c_984, plain, (![C_244, E_245, B_243, A_242, D_246]: (v1_funct_1(k3_tmap_1(A_242, B_243, k1_tsep_1(A_242, C_244, D_246), D_246, E_245)) | ~v5_pre_topc(E_245, k1_tsep_1(A_242, C_244, D_246), B_243) | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_242, C_244, D_246)), u1_struct_0(B_243)))) | ~v1_funct_2(E_245, u1_struct_0(k1_tsep_1(A_242, C_244, D_246)), u1_struct_0(B_243)) | ~v1_funct_1(E_245) | ~r4_tsep_1(A_242, C_244, D_246) | ~m1_pre_topc(D_246, A_242) | v2_struct_0(D_246) | ~m1_pre_topc(C_244, A_242) | v2_struct_0(C_244) | ~l1_pre_topc(B_243) | ~v2_pre_topc(B_243) | v2_struct_0(B_243) | ~l1_pre_topc(A_242) | ~v2_pre_topc(A_242) | v2_struct_0(A_242))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_986, plain, (![B_243, E_245]: (v1_funct_1(k3_tmap_1('#skF_1', B_243, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_245)) | ~v5_pre_topc(E_245, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_243) | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_243)))) | ~v1_funct_2(E_245, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_243)) | ~v1_funct_1(E_245) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_243) | ~v2_pre_topc(B_243) | v2_struct_0(B_243) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_984])).
% 7.89/2.64  tff(c_988, plain, (![B_243, E_245]: (v1_funct_1(k3_tmap_1('#skF_1', B_243, '#skF_1', '#skF_5', E_245)) | ~v5_pre_topc(E_245, '#skF_1', B_243) | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_243)))) | ~v1_funct_2(E_245, u1_struct_0('#skF_1'), u1_struct_0(B_243)) | ~v1_funct_1(E_245) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_243) | ~v2_pre_topc(B_243) | v2_struct_0(B_243) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_34, c_34, c_34, c_986])).
% 7.89/2.64  tff(c_989, plain, (![B_243, E_245]: (v1_funct_1(k3_tmap_1('#skF_1', B_243, '#skF_1', '#skF_5', E_245)) | ~v5_pre_topc(E_245, '#skF_1', B_243) | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_243)))) | ~v1_funct_2(E_245, u1_struct_0('#skF_1'), u1_struct_0(B_243)) | ~v1_funct_1(E_245) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~l1_pre_topc(B_243) | ~v2_pre_topc(B_243) | v2_struct_0(B_243))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_988])).
% 7.89/2.64  tff(c_1096, plain, (~r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_989])).
% 7.89/2.64  tff(c_1099, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~v1_tsep_1('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1096])).
% 7.89/2.64  tff(c_1102, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_42, c_38, c_36, c_1099])).
% 7.89/2.64  tff(c_1104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1102])).
% 7.89/2.64  tff(c_1106, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_989])).
% 7.89/2.64  tff(c_1331, plain, (![B_292, C_293, D_295, A_291, E_294]: (m1_subset_1(k3_tmap_1(A_291, B_292, k1_tsep_1(A_291, C_293, D_295), C_293, E_294), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_293), u1_struct_0(B_292)))) | ~v5_pre_topc(E_294, k1_tsep_1(A_291, C_293, D_295), B_292) | ~m1_subset_1(E_294, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_291, C_293, D_295)), u1_struct_0(B_292)))) | ~v1_funct_2(E_294, u1_struct_0(k1_tsep_1(A_291, C_293, D_295)), u1_struct_0(B_292)) | ~v1_funct_1(E_294) | ~r4_tsep_1(A_291, C_293, D_295) | ~m1_pre_topc(D_295, A_291) | v2_struct_0(D_295) | ~m1_pre_topc(C_293, A_291) | v2_struct_0(C_293) | ~l1_pre_topc(B_292) | ~v2_pre_topc(B_292) | v2_struct_0(B_292) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_1376, plain, (![B_292, E_294]: (m1_subset_1(k3_tmap_1('#skF_1', B_292, '#skF_1', '#skF_4', E_294), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_292)))) | ~v5_pre_topc(E_294, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_292) | ~m1_subset_1(E_294, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_292)))) | ~v1_funct_2(E_294, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_292)) | ~v1_funct_1(E_294) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_292) | ~v2_pre_topc(B_292) | v2_struct_0(B_292) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1331])).
% 7.89/2.64  tff(c_1404, plain, (![B_292, E_294]: (m1_subset_1(k3_tmap_1('#skF_1', B_292, '#skF_1', '#skF_4', E_294), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_292)))) | ~v5_pre_topc(E_294, '#skF_1', B_292) | ~m1_subset_1(E_294, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_292)))) | ~v1_funct_2(E_294, u1_struct_0('#skF_1'), u1_struct_0(B_292)) | ~v1_funct_1(E_294) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_292) | ~v2_pre_topc(B_292) | v2_struct_0(B_292) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_1106, c_34, c_34, c_34, c_1376])).
% 7.89/2.64  tff(c_1406, plain, (![B_296, E_297]: (m1_subset_1(k3_tmap_1('#skF_1', B_296, '#skF_1', '#skF_4', E_297), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_296)))) | ~v5_pre_topc(E_297, '#skF_1', B_296) | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_296)))) | ~v1_funct_2(E_297, u1_struct_0('#skF_1'), u1_struct_0(B_296)) | ~v1_funct_1(E_297) | ~l1_pre_topc(B_296) | ~v2_pre_topc(B_296) | v2_struct_0(B_296))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_1404])).
% 7.89/2.64  tff(c_1413, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1086, c_1406])).
% 7.89/2.64  tff(c_1418, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_919, c_1413])).
% 7.89/2.64  tff(c_1420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_920, c_1418])).
% 7.89/2.64  tff(c_1422, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_80])).
% 7.89/2.64  tff(c_1421, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_80])).
% 7.89/2.64  tff(c_1441, plain, (![D_308, B_306, E_307, A_310, C_309]: (k3_tmap_1(A_310, B_306, C_309, D_308, E_307)=k2_partfun1(u1_struct_0(C_309), u1_struct_0(B_306), E_307, u1_struct_0(D_308)) | ~m1_pre_topc(D_308, C_309) | ~m1_subset_1(E_307, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_309), u1_struct_0(B_306)))) | ~v1_funct_2(E_307, u1_struct_0(C_309), u1_struct_0(B_306)) | ~v1_funct_1(E_307) | ~m1_pre_topc(D_308, A_310) | ~m1_pre_topc(C_309, A_310) | ~l1_pre_topc(B_306) | ~v2_pre_topc(B_306) | v2_struct_0(B_306) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310) | v2_struct_0(A_310))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.89/2.64  tff(c_1443, plain, (![A_310, D_308]: (k3_tmap_1(A_310, '#skF_2', '#skF_1', D_308, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_308)) | ~m1_pre_topc(D_308, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_308, A_310) | ~m1_pre_topc('#skF_1', A_310) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310) | v2_struct_0(A_310))), inference(resolution, [status(thm)], [c_48, c_1441])).
% 7.89/2.64  tff(c_1446, plain, (![A_310, D_308]: (k3_tmap_1(A_310, '#skF_2', '#skF_1', D_308, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_308)) | ~m1_pre_topc(D_308, '#skF_1') | ~m1_pre_topc(D_308, A_310) | ~m1_pre_topc('#skF_1', A_310) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310) | v2_struct_0(A_310))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_1443])).
% 7.89/2.64  tff(c_1448, plain, (![A_311, D_312]: (k3_tmap_1(A_311, '#skF_2', '#skF_1', D_312, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_312)) | ~m1_pre_topc(D_312, '#skF_1') | ~m1_pre_topc(D_312, A_311) | ~m1_pre_topc('#skF_1', A_311) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311) | v2_struct_0(A_311))), inference(negUnitSimplification, [status(thm)], [c_58, c_1446])).
% 7.89/2.64  tff(c_1452, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1448])).
% 7.89/2.64  tff(c_1458, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_36, c_1452])).
% 7.89/2.64  tff(c_1459, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_1458])).
% 7.89/2.64  tff(c_1464, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_1459])).
% 7.89/2.64  tff(c_1467, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1464])).
% 7.89/2.64  tff(c_1471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_1467])).
% 7.89/2.64  tff(c_1472, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_1459])).
% 7.89/2.64  tff(c_1425, plain, (![A_301, B_302, C_303, D_304]: (k2_partfun1(u1_struct_0(A_301), u1_struct_0(B_302), C_303, u1_struct_0(D_304))=k2_tmap_1(A_301, B_302, C_303, D_304) | ~m1_pre_topc(D_304, A_301) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_301), u1_struct_0(B_302)))) | ~v1_funct_2(C_303, u1_struct_0(A_301), u1_struct_0(B_302)) | ~v1_funct_1(C_303) | ~l1_pre_topc(B_302) | ~v2_pre_topc(B_302) | v2_struct_0(B_302) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.89/2.64  tff(c_1427, plain, (![D_304]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_304))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_304) | ~m1_pre_topc(D_304, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_1425])).
% 7.89/2.64  tff(c_1430, plain, (![D_304]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_304))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_304) | ~m1_pre_topc(D_304, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_1427])).
% 7.89/2.64  tff(c_1431, plain, (![D_304]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_304))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_304) | ~m1_pre_topc(D_304, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_1430])).
% 7.89/2.64  tff(c_1489, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1472, c_1431])).
% 7.89/2.64  tff(c_1496, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1489])).
% 7.89/2.64  tff(c_1480, plain, (![D_317, C_315, B_314, E_316, A_313]: (v1_funct_1(k3_tmap_1(A_313, B_314, k1_tsep_1(A_313, C_315, D_317), D_317, E_316)) | ~v5_pre_topc(E_316, k1_tsep_1(A_313, C_315, D_317), B_314) | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_313, C_315, D_317)), u1_struct_0(B_314)))) | ~v1_funct_2(E_316, u1_struct_0(k1_tsep_1(A_313, C_315, D_317)), u1_struct_0(B_314)) | ~v1_funct_1(E_316) | ~r4_tsep_1(A_313, C_315, D_317) | ~m1_pre_topc(D_317, A_313) | v2_struct_0(D_317) | ~m1_pre_topc(C_315, A_313) | v2_struct_0(C_315) | ~l1_pre_topc(B_314) | ~v2_pre_topc(B_314) | v2_struct_0(B_314) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_1482, plain, (![B_314, E_316]: (v1_funct_1(k3_tmap_1('#skF_1', B_314, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_316)) | ~v5_pre_topc(E_316, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_314) | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_314)))) | ~v1_funct_2(E_316, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_314)) | ~v1_funct_1(E_316) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_314) | ~v2_pre_topc(B_314) | v2_struct_0(B_314) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1480])).
% 7.89/2.64  tff(c_1484, plain, (![B_314, E_316]: (v1_funct_1(k3_tmap_1('#skF_1', B_314, '#skF_1', '#skF_5', E_316)) | ~v5_pre_topc(E_316, '#skF_1', B_314) | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_314)))) | ~v1_funct_2(E_316, u1_struct_0('#skF_1'), u1_struct_0(B_314)) | ~v1_funct_1(E_316) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_314) | ~v2_pre_topc(B_314) | v2_struct_0(B_314) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_34, c_34, c_34, c_1482])).
% 7.89/2.64  tff(c_1485, plain, (![B_314, E_316]: (v1_funct_1(k3_tmap_1('#skF_1', B_314, '#skF_1', '#skF_5', E_316)) | ~v5_pre_topc(E_316, '#skF_1', B_314) | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_314)))) | ~v1_funct_2(E_316, u1_struct_0('#skF_1'), u1_struct_0(B_314)) | ~v1_funct_1(E_316) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~l1_pre_topc(B_314) | ~v2_pre_topc(B_314) | v2_struct_0(B_314))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_1484])).
% 7.89/2.64  tff(c_1602, plain, (~r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1485])).
% 7.89/2.64  tff(c_1605, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~v1_tsep_1('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1602])).
% 7.89/2.64  tff(c_1608, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_42, c_38, c_36, c_1605])).
% 7.89/2.64  tff(c_1610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1608])).
% 7.89/2.64  tff(c_1612, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1485])).
% 7.89/2.64  tff(c_1873, plain, (![A_364, D_368, E_367, C_366, B_365]: (m1_subset_1(k3_tmap_1(A_364, B_365, k1_tsep_1(A_364, C_366, D_368), D_368, E_367), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_368), u1_struct_0(B_365)))) | ~v5_pre_topc(E_367, k1_tsep_1(A_364, C_366, D_368), B_365) | ~m1_subset_1(E_367, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_364, C_366, D_368)), u1_struct_0(B_365)))) | ~v1_funct_2(E_367, u1_struct_0(k1_tsep_1(A_364, C_366, D_368)), u1_struct_0(B_365)) | ~v1_funct_1(E_367) | ~r4_tsep_1(A_364, C_366, D_368) | ~m1_pre_topc(D_368, A_364) | v2_struct_0(D_368) | ~m1_pre_topc(C_366, A_364) | v2_struct_0(C_366) | ~l1_pre_topc(B_365) | ~v2_pre_topc(B_365) | v2_struct_0(B_365) | ~l1_pre_topc(A_364) | ~v2_pre_topc(A_364) | v2_struct_0(A_364))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_1918, plain, (![B_365, E_367]: (m1_subset_1(k3_tmap_1('#skF_1', B_365, '#skF_1', '#skF_5', E_367), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_365)))) | ~v5_pre_topc(E_367, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_365) | ~m1_subset_1(E_367, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_365)))) | ~v1_funct_2(E_367, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_365)) | ~v1_funct_1(E_367) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_365) | ~v2_pre_topc(B_365) | v2_struct_0(B_365) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1873])).
% 7.89/2.64  tff(c_1946, plain, (![B_365, E_367]: (m1_subset_1(k3_tmap_1('#skF_1', B_365, '#skF_1', '#skF_5', E_367), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_365)))) | ~v5_pre_topc(E_367, '#skF_1', B_365) | ~m1_subset_1(E_367, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_365)))) | ~v1_funct_2(E_367, u1_struct_0('#skF_1'), u1_struct_0(B_365)) | ~v1_funct_1(E_367) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_365) | ~v2_pre_topc(B_365) | v2_struct_0(B_365) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_1612, c_34, c_34, c_34, c_1918])).
% 7.89/2.64  tff(c_1963, plain, (![B_371, E_372]: (m1_subset_1(k3_tmap_1('#skF_1', B_371, '#skF_1', '#skF_5', E_372), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_371)))) | ~v5_pre_topc(E_372, '#skF_1', B_371) | ~m1_subset_1(E_372, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_371)))) | ~v1_funct_2(E_372, u1_struct_0('#skF_1'), u1_struct_0(B_371)) | ~v1_funct_1(E_372) | ~l1_pre_topc(B_371) | ~v2_pre_topc(B_371) | v2_struct_0(B_371))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_1946])).
% 7.89/2.64  tff(c_1970, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1496, c_1963])).
% 7.89/2.64  tff(c_1975, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_1421, c_1970])).
% 7.89/2.64  tff(c_1977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1422, c_1975])).
% 7.89/2.64  tff(c_1979, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_100])).
% 7.89/2.64  tff(c_1978, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_100])).
% 7.89/2.64  tff(c_1999, plain, (![D_383, A_385, B_381, E_382, C_384]: (k3_tmap_1(A_385, B_381, C_384, D_383, E_382)=k2_partfun1(u1_struct_0(C_384), u1_struct_0(B_381), E_382, u1_struct_0(D_383)) | ~m1_pre_topc(D_383, C_384) | ~m1_subset_1(E_382, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_384), u1_struct_0(B_381)))) | ~v1_funct_2(E_382, u1_struct_0(C_384), u1_struct_0(B_381)) | ~v1_funct_1(E_382) | ~m1_pre_topc(D_383, A_385) | ~m1_pre_topc(C_384, A_385) | ~l1_pre_topc(B_381) | ~v2_pre_topc(B_381) | v2_struct_0(B_381) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.89/2.64  tff(c_2001, plain, (![A_385, D_383]: (k3_tmap_1(A_385, '#skF_2', '#skF_1', D_383, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_383)) | ~m1_pre_topc(D_383, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_383, A_385) | ~m1_pre_topc('#skF_1', A_385) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385))), inference(resolution, [status(thm)], [c_48, c_1999])).
% 7.89/2.64  tff(c_2004, plain, (![A_385, D_383]: (k3_tmap_1(A_385, '#skF_2', '#skF_1', D_383, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_383)) | ~m1_pre_topc(D_383, '#skF_1') | ~m1_pre_topc(D_383, A_385) | ~m1_pre_topc('#skF_1', A_385) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2001])).
% 7.89/2.64  tff(c_2006, plain, (![A_386, D_387]: (k3_tmap_1(A_386, '#skF_2', '#skF_1', D_387, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_387)) | ~m1_pre_topc(D_387, '#skF_1') | ~m1_pre_topc(D_387, A_386) | ~m1_pre_topc('#skF_1', A_386) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | v2_struct_0(A_386))), inference(negUnitSimplification, [status(thm)], [c_58, c_2004])).
% 7.89/2.64  tff(c_2010, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2006])).
% 7.89/2.64  tff(c_2016, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_36, c_2010])).
% 7.89/2.64  tff(c_2017, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_2016])).
% 7.89/2.64  tff(c_2022, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_2017])).
% 7.89/2.64  tff(c_2025, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2022])).
% 7.89/2.64  tff(c_2029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_2025])).
% 7.89/2.64  tff(c_2030, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_2017])).
% 7.89/2.64  tff(c_1983, plain, (![A_376, B_377, C_378, D_379]: (k2_partfun1(u1_struct_0(A_376), u1_struct_0(B_377), C_378, u1_struct_0(D_379))=k2_tmap_1(A_376, B_377, C_378, D_379) | ~m1_pre_topc(D_379, A_376) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_376), u1_struct_0(B_377)))) | ~v1_funct_2(C_378, u1_struct_0(A_376), u1_struct_0(B_377)) | ~v1_funct_1(C_378) | ~l1_pre_topc(B_377) | ~v2_pre_topc(B_377) | v2_struct_0(B_377) | ~l1_pre_topc(A_376) | ~v2_pre_topc(A_376) | v2_struct_0(A_376))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.89/2.64  tff(c_1985, plain, (![D_379]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_379))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_379) | ~m1_pre_topc(D_379, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_1983])).
% 7.89/2.64  tff(c_1988, plain, (![D_379]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_379))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_379) | ~m1_pre_topc(D_379, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_1985])).
% 7.89/2.64  tff(c_1989, plain, (![D_379]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_379))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_379) | ~m1_pre_topc(D_379, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_1988])).
% 7.89/2.64  tff(c_2131, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2030, c_1989])).
% 7.89/2.64  tff(c_2138, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2131])).
% 7.89/2.64  tff(c_2147, plain, (![B_394, D_397, A_393, E_396, C_395]: (v1_funct_1(k3_tmap_1(A_393, B_394, k1_tsep_1(A_393, C_395, D_397), C_395, E_396)) | ~v5_pre_topc(E_396, k1_tsep_1(A_393, C_395, D_397), B_394) | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_393, C_395, D_397)), u1_struct_0(B_394)))) | ~v1_funct_2(E_396, u1_struct_0(k1_tsep_1(A_393, C_395, D_397)), u1_struct_0(B_394)) | ~v1_funct_1(E_396) | ~r4_tsep_1(A_393, C_395, D_397) | ~m1_pre_topc(D_397, A_393) | v2_struct_0(D_397) | ~m1_pre_topc(C_395, A_393) | v2_struct_0(C_395) | ~l1_pre_topc(B_394) | ~v2_pre_topc(B_394) | v2_struct_0(B_394) | ~l1_pre_topc(A_393) | ~v2_pre_topc(A_393) | v2_struct_0(A_393))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_2149, plain, (![B_394, E_396]: (v1_funct_1(k3_tmap_1('#skF_1', B_394, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_396)) | ~v5_pre_topc(E_396, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_394) | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_394)))) | ~v1_funct_2(E_396, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_394)) | ~v1_funct_1(E_396) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_394) | ~v2_pre_topc(B_394) | v2_struct_0(B_394) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2147])).
% 7.89/2.64  tff(c_2151, plain, (![B_394, E_396]: (v1_funct_1(k3_tmap_1('#skF_1', B_394, '#skF_1', '#skF_4', E_396)) | ~v5_pre_topc(E_396, '#skF_1', B_394) | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_394)))) | ~v1_funct_2(E_396, u1_struct_0('#skF_1'), u1_struct_0(B_394)) | ~v1_funct_1(E_396) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_394) | ~v2_pre_topc(B_394) | v2_struct_0(B_394) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_34, c_34, c_34, c_2149])).
% 7.89/2.64  tff(c_2152, plain, (![B_394, E_396]: (v1_funct_1(k3_tmap_1('#skF_1', B_394, '#skF_1', '#skF_4', E_396)) | ~v5_pre_topc(E_396, '#skF_1', B_394) | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_394)))) | ~v1_funct_2(E_396, u1_struct_0('#skF_1'), u1_struct_0(B_394)) | ~v1_funct_1(E_396) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~l1_pre_topc(B_394) | ~v2_pre_topc(B_394) | v2_struct_0(B_394))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_2151])).
% 7.89/2.64  tff(c_2263, plain, (~r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_2152])).
% 7.89/2.64  tff(c_2267, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~v1_tsep_1('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2263])).
% 7.89/2.64  tff(c_2270, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_42, c_38, c_36, c_2267])).
% 7.89/2.64  tff(c_2272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2270])).
% 7.89/2.64  tff(c_2274, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_2152])).
% 7.89/2.64  tff(c_2330, plain, (![C_427, D_429, A_425, B_426, E_428]: (v1_funct_2(k3_tmap_1(A_425, B_426, k1_tsep_1(A_425, C_427, D_429), D_429, E_428), u1_struct_0(D_429), u1_struct_0(B_426)) | ~v5_pre_topc(E_428, k1_tsep_1(A_425, C_427, D_429), B_426) | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_425, C_427, D_429)), u1_struct_0(B_426)))) | ~v1_funct_2(E_428, u1_struct_0(k1_tsep_1(A_425, C_427, D_429)), u1_struct_0(B_426)) | ~v1_funct_1(E_428) | ~r4_tsep_1(A_425, C_427, D_429) | ~m1_pre_topc(D_429, A_425) | v2_struct_0(D_429) | ~m1_pre_topc(C_427, A_425) | v2_struct_0(C_427) | ~l1_pre_topc(B_426) | ~v2_pre_topc(B_426) | v2_struct_0(B_426) | ~l1_pre_topc(A_425) | ~v2_pre_topc(A_425) | v2_struct_0(A_425))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_2332, plain, (![B_426, E_428]: (v1_funct_2(k3_tmap_1('#skF_1', B_426, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_428), u1_struct_0('#skF_5'), u1_struct_0(B_426)) | ~v5_pre_topc(E_428, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_426) | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_426)))) | ~v1_funct_2(E_428, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_426)) | ~v1_funct_1(E_428) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_426) | ~v2_pre_topc(B_426) | v2_struct_0(B_426) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2330])).
% 7.89/2.64  tff(c_2334, plain, (![B_426, E_428]: (v1_funct_2(k3_tmap_1('#skF_1', B_426, '#skF_1', '#skF_5', E_428), u1_struct_0('#skF_5'), u1_struct_0(B_426)) | ~v5_pre_topc(E_428, '#skF_1', B_426) | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_426)))) | ~v1_funct_2(E_428, u1_struct_0('#skF_1'), u1_struct_0(B_426)) | ~v1_funct_1(E_428) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_426) | ~v2_pre_topc(B_426) | v2_struct_0(B_426) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_2274, c_34, c_34, c_34, c_2332])).
% 7.89/2.64  tff(c_2336, plain, (![B_430, E_431]: (v1_funct_2(k3_tmap_1('#skF_1', B_430, '#skF_1', '#skF_5', E_431), u1_struct_0('#skF_5'), u1_struct_0(B_430)) | ~v5_pre_topc(E_431, '#skF_1', B_430) | ~m1_subset_1(E_431, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_430)))) | ~v1_funct_2(E_431, u1_struct_0('#skF_1'), u1_struct_0(B_430)) | ~v1_funct_1(E_431) | ~l1_pre_topc(B_430) | ~v2_pre_topc(B_430) | v2_struct_0(B_430))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_2334])).
% 7.89/2.64  tff(c_2338, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_2336])).
% 7.89/2.64  tff(c_2341, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_1978, c_2138, c_2338])).
% 7.89/2.64  tff(c_2343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1979, c_2341])).
% 7.89/2.64  tff(c_2345, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_140])).
% 7.89/2.64  tff(c_2344, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_140])).
% 7.89/2.64  tff(c_2366, plain, (![C_443, B_440, A_444, E_441, D_442]: (k3_tmap_1(A_444, B_440, C_443, D_442, E_441)=k2_partfun1(u1_struct_0(C_443), u1_struct_0(B_440), E_441, u1_struct_0(D_442)) | ~m1_pre_topc(D_442, C_443) | ~m1_subset_1(E_441, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_443), u1_struct_0(B_440)))) | ~v1_funct_2(E_441, u1_struct_0(C_443), u1_struct_0(B_440)) | ~v1_funct_1(E_441) | ~m1_pre_topc(D_442, A_444) | ~m1_pre_topc(C_443, A_444) | ~l1_pre_topc(B_440) | ~v2_pre_topc(B_440) | v2_struct_0(B_440) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.89/2.64  tff(c_2368, plain, (![A_444, D_442]: (k3_tmap_1(A_444, '#skF_2', '#skF_1', D_442, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_442)) | ~m1_pre_topc(D_442, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_442, A_444) | ~m1_pre_topc('#skF_1', A_444) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(resolution, [status(thm)], [c_48, c_2366])).
% 7.89/2.64  tff(c_2371, plain, (![A_444, D_442]: (k3_tmap_1(A_444, '#skF_2', '#skF_1', D_442, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_442)) | ~m1_pre_topc(D_442, '#skF_1') | ~m1_pre_topc(D_442, A_444) | ~m1_pre_topc('#skF_1', A_444) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2368])).
% 7.89/2.64  tff(c_2373, plain, (![A_445, D_446]: (k3_tmap_1(A_445, '#skF_2', '#skF_1', D_446, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_446)) | ~m1_pre_topc(D_446, '#skF_1') | ~m1_pre_topc(D_446, A_445) | ~m1_pre_topc('#skF_1', A_445) | ~l1_pre_topc(A_445) | ~v2_pre_topc(A_445) | v2_struct_0(A_445))), inference(negUnitSimplification, [status(thm)], [c_58, c_2371])).
% 7.89/2.64  tff(c_2377, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2373])).
% 7.89/2.64  tff(c_2383, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_36, c_2377])).
% 7.89/2.64  tff(c_2384, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_2383])).
% 7.89/2.64  tff(c_2389, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_2384])).
% 7.89/2.64  tff(c_2392, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2389])).
% 7.89/2.64  tff(c_2396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_2392])).
% 7.89/2.64  tff(c_2398, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_2384])).
% 7.89/2.64  tff(c_2379, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2373])).
% 7.89/2.64  tff(c_2387, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_2379])).
% 7.89/2.64  tff(c_2388, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_2387])).
% 7.89/2.64  tff(c_2484, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_2388])).
% 7.89/2.64  tff(c_2350, plain, (![A_435, B_436, C_437, D_438]: (k2_partfun1(u1_struct_0(A_435), u1_struct_0(B_436), C_437, u1_struct_0(D_438))=k2_tmap_1(A_435, B_436, C_437, D_438) | ~m1_pre_topc(D_438, A_435) | ~m1_subset_1(C_437, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_435), u1_struct_0(B_436)))) | ~v1_funct_2(C_437, u1_struct_0(A_435), u1_struct_0(B_436)) | ~v1_funct_1(C_437) | ~l1_pre_topc(B_436) | ~v2_pre_topc(B_436) | v2_struct_0(B_436) | ~l1_pre_topc(A_435) | ~v2_pre_topc(A_435) | v2_struct_0(A_435))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.89/2.64  tff(c_2352, plain, (![D_438]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_438))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_438) | ~m1_pre_topc(D_438, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_2350])).
% 7.89/2.64  tff(c_2355, plain, (![D_438]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_438))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_438) | ~m1_pre_topc(D_438, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_2352])).
% 7.89/2.64  tff(c_2356, plain, (![D_438]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_438))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_438) | ~m1_pre_topc(D_438, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_2355])).
% 7.89/2.64  tff(c_2488, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2484, c_2356])).
% 7.89/2.64  tff(c_2495, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2488])).
% 7.89/2.64  tff(c_2405, plain, (![A_447, D_451, B_448, C_449, E_450]: (v1_funct_1(k3_tmap_1(A_447, B_448, k1_tsep_1(A_447, C_449, D_451), C_449, E_450)) | ~v5_pre_topc(E_450, k1_tsep_1(A_447, C_449, D_451), B_448) | ~m1_subset_1(E_450, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_447, C_449, D_451)), u1_struct_0(B_448)))) | ~v1_funct_2(E_450, u1_struct_0(k1_tsep_1(A_447, C_449, D_451)), u1_struct_0(B_448)) | ~v1_funct_1(E_450) | ~r4_tsep_1(A_447, C_449, D_451) | ~m1_pre_topc(D_451, A_447) | v2_struct_0(D_451) | ~m1_pre_topc(C_449, A_447) | v2_struct_0(C_449) | ~l1_pre_topc(B_448) | ~v2_pre_topc(B_448) | v2_struct_0(B_448) | ~l1_pre_topc(A_447) | ~v2_pre_topc(A_447) | v2_struct_0(A_447))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_2407, plain, (![B_448, E_450]: (v1_funct_1(k3_tmap_1('#skF_1', B_448, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_450)) | ~v5_pre_topc(E_450, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_448) | ~m1_subset_1(E_450, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_448)))) | ~v1_funct_2(E_450, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_448)) | ~v1_funct_1(E_450) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_448) | ~v2_pre_topc(B_448) | v2_struct_0(B_448) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2405])).
% 7.89/2.64  tff(c_2409, plain, (![B_448, E_450]: (v1_funct_1(k3_tmap_1('#skF_1', B_448, '#skF_1', '#skF_4', E_450)) | ~v5_pre_topc(E_450, '#skF_1', B_448) | ~m1_subset_1(E_450, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_448)))) | ~v1_funct_2(E_450, u1_struct_0('#skF_1'), u1_struct_0(B_448)) | ~v1_funct_1(E_450) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_448) | ~v2_pre_topc(B_448) | v2_struct_0(B_448) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_34, c_34, c_34, c_2407])).
% 7.89/2.64  tff(c_2410, plain, (![B_448, E_450]: (v1_funct_1(k3_tmap_1('#skF_1', B_448, '#skF_1', '#skF_4', E_450)) | ~v5_pre_topc(E_450, '#skF_1', B_448) | ~m1_subset_1(E_450, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_448)))) | ~v1_funct_2(E_450, u1_struct_0('#skF_1'), u1_struct_0(B_448)) | ~v1_funct_1(E_450) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~l1_pre_topc(B_448) | ~v2_pre_topc(B_448) | v2_struct_0(B_448))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_2409])).
% 7.89/2.64  tff(c_2527, plain, (~r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_2410])).
% 7.89/2.64  tff(c_2530, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~v1_tsep_1('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2527])).
% 7.89/2.64  tff(c_2533, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_42, c_38, c_36, c_2530])).
% 7.89/2.64  tff(c_2535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2533])).
% 7.89/2.64  tff(c_2537, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_2410])).
% 7.89/2.64  tff(c_2669, plain, (![C_479, D_481, B_478, E_480, A_477]: (v1_funct_2(k3_tmap_1(A_477, B_478, k1_tsep_1(A_477, C_479, D_481), C_479, E_480), u1_struct_0(C_479), u1_struct_0(B_478)) | ~v5_pre_topc(E_480, k1_tsep_1(A_477, C_479, D_481), B_478) | ~m1_subset_1(E_480, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_477, C_479, D_481)), u1_struct_0(B_478)))) | ~v1_funct_2(E_480, u1_struct_0(k1_tsep_1(A_477, C_479, D_481)), u1_struct_0(B_478)) | ~v1_funct_1(E_480) | ~r4_tsep_1(A_477, C_479, D_481) | ~m1_pre_topc(D_481, A_477) | v2_struct_0(D_481) | ~m1_pre_topc(C_479, A_477) | v2_struct_0(C_479) | ~l1_pre_topc(B_478) | ~v2_pre_topc(B_478) | v2_struct_0(B_478) | ~l1_pre_topc(A_477) | ~v2_pre_topc(A_477) | v2_struct_0(A_477))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_2671, plain, (![B_478, E_480]: (v1_funct_2(k3_tmap_1('#skF_1', B_478, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_480), u1_struct_0('#skF_4'), u1_struct_0(B_478)) | ~v5_pre_topc(E_480, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_478) | ~m1_subset_1(E_480, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_478)))) | ~v1_funct_2(E_480, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_478)) | ~v1_funct_1(E_480) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_478) | ~v2_pre_topc(B_478) | v2_struct_0(B_478) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2669])).
% 7.89/2.64  tff(c_2673, plain, (![B_478, E_480]: (v1_funct_2(k3_tmap_1('#skF_1', B_478, '#skF_1', '#skF_4', E_480), u1_struct_0('#skF_4'), u1_struct_0(B_478)) | ~v5_pre_topc(E_480, '#skF_1', B_478) | ~m1_subset_1(E_480, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_478)))) | ~v1_funct_2(E_480, u1_struct_0('#skF_1'), u1_struct_0(B_478)) | ~v1_funct_1(E_480) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_478) | ~v2_pre_topc(B_478) | v2_struct_0(B_478) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_2537, c_34, c_34, c_34, c_2671])).
% 7.89/2.64  tff(c_2675, plain, (![B_482, E_483]: (v1_funct_2(k3_tmap_1('#skF_1', B_482, '#skF_1', '#skF_4', E_483), u1_struct_0('#skF_4'), u1_struct_0(B_482)) | ~v5_pre_topc(E_483, '#skF_1', B_482) | ~m1_subset_1(E_483, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_482)))) | ~v1_funct_2(E_483, u1_struct_0('#skF_1'), u1_struct_0(B_482)) | ~v1_funct_1(E_483) | ~l1_pre_topc(B_482) | ~v2_pre_topc(B_482) | v2_struct_0(B_482))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_2673])).
% 7.89/2.64  tff(c_2677, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_2675])).
% 7.89/2.64  tff(c_2680, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2344, c_2495, c_2677])).
% 7.89/2.64  tff(c_2682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2345, c_2680])).
% 7.89/2.64  tff(c_2684, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_130])).
% 7.89/2.64  tff(c_2683, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_130])).
% 7.89/2.64  tff(c_2708, plain, (![E_493, B_492, C_495, A_496, D_494]: (k3_tmap_1(A_496, B_492, C_495, D_494, E_493)=k2_partfun1(u1_struct_0(C_495), u1_struct_0(B_492), E_493, u1_struct_0(D_494)) | ~m1_pre_topc(D_494, C_495) | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_495), u1_struct_0(B_492)))) | ~v1_funct_2(E_493, u1_struct_0(C_495), u1_struct_0(B_492)) | ~v1_funct_1(E_493) | ~m1_pre_topc(D_494, A_496) | ~m1_pre_topc(C_495, A_496) | ~l1_pre_topc(B_492) | ~v2_pre_topc(B_492) | v2_struct_0(B_492) | ~l1_pre_topc(A_496) | ~v2_pre_topc(A_496) | v2_struct_0(A_496))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.89/2.64  tff(c_2710, plain, (![A_496, D_494]: (k3_tmap_1(A_496, '#skF_2', '#skF_1', D_494, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_494)) | ~m1_pre_topc(D_494, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_494, A_496) | ~m1_pre_topc('#skF_1', A_496) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_496) | ~v2_pre_topc(A_496) | v2_struct_0(A_496))), inference(resolution, [status(thm)], [c_48, c_2708])).
% 7.89/2.64  tff(c_2713, plain, (![A_496, D_494]: (k3_tmap_1(A_496, '#skF_2', '#skF_1', D_494, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_494)) | ~m1_pre_topc(D_494, '#skF_1') | ~m1_pre_topc(D_494, A_496) | ~m1_pre_topc('#skF_1', A_496) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_496) | ~v2_pre_topc(A_496) | v2_struct_0(A_496))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2710])).
% 7.89/2.64  tff(c_2715, plain, (![A_497, D_498]: (k3_tmap_1(A_497, '#skF_2', '#skF_1', D_498, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_498)) | ~m1_pre_topc(D_498, '#skF_1') | ~m1_pre_topc(D_498, A_497) | ~m1_pre_topc('#skF_1', A_497) | ~l1_pre_topc(A_497) | ~v2_pre_topc(A_497) | v2_struct_0(A_497))), inference(negUnitSimplification, [status(thm)], [c_58, c_2713])).
% 7.89/2.64  tff(c_2719, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2715])).
% 7.89/2.64  tff(c_2725, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_36, c_2719])).
% 7.89/2.64  tff(c_2726, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_2725])).
% 7.89/2.64  tff(c_2731, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_2726])).
% 7.89/2.64  tff(c_2734, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_2731])).
% 7.89/2.64  tff(c_2738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_2734])).
% 7.89/2.64  tff(c_2740, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_2726])).
% 7.89/2.64  tff(c_2721, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2715])).
% 7.89/2.64  tff(c_2729, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_2721])).
% 7.89/2.64  tff(c_2730, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_2729])).
% 7.89/2.64  tff(c_2826, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2740, c_2730])).
% 7.89/2.64  tff(c_2690, plain, (![A_487, B_488, C_489, D_490]: (k2_partfun1(u1_struct_0(A_487), u1_struct_0(B_488), C_489, u1_struct_0(D_490))=k2_tmap_1(A_487, B_488, C_489, D_490) | ~m1_pre_topc(D_490, A_487) | ~m1_subset_1(C_489, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_487), u1_struct_0(B_488)))) | ~v1_funct_2(C_489, u1_struct_0(A_487), u1_struct_0(B_488)) | ~v1_funct_1(C_489) | ~l1_pre_topc(B_488) | ~v2_pre_topc(B_488) | v2_struct_0(B_488) | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.89/2.64  tff(c_2692, plain, (![D_490]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_490))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_490) | ~m1_pre_topc(D_490, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_2690])).
% 7.89/2.64  tff(c_2695, plain, (![D_490]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_490))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_490) | ~m1_pre_topc(D_490, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_2692])).
% 7.89/2.64  tff(c_2696, plain, (![D_490]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_490))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_490) | ~m1_pre_topc(D_490, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_2695])).
% 7.89/2.64  tff(c_2830, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2826, c_2696])).
% 7.89/2.64  tff(c_2837, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2830])).
% 7.89/2.64  tff(c_2747, plain, (![B_500, E_502, D_503, C_501, A_499]: (v1_funct_1(k3_tmap_1(A_499, B_500, k1_tsep_1(A_499, C_501, D_503), D_503, E_502)) | ~v5_pre_topc(E_502, k1_tsep_1(A_499, C_501, D_503), B_500) | ~m1_subset_1(E_502, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_499, C_501, D_503)), u1_struct_0(B_500)))) | ~v1_funct_2(E_502, u1_struct_0(k1_tsep_1(A_499, C_501, D_503)), u1_struct_0(B_500)) | ~v1_funct_1(E_502) | ~r4_tsep_1(A_499, C_501, D_503) | ~m1_pre_topc(D_503, A_499) | v2_struct_0(D_503) | ~m1_pre_topc(C_501, A_499) | v2_struct_0(C_501) | ~l1_pre_topc(B_500) | ~v2_pre_topc(B_500) | v2_struct_0(B_500) | ~l1_pre_topc(A_499) | ~v2_pre_topc(A_499) | v2_struct_0(A_499))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_2749, plain, (![B_500, E_502]: (v1_funct_1(k3_tmap_1('#skF_1', B_500, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_502)) | ~v5_pre_topc(E_502, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_500) | ~m1_subset_1(E_502, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_500)))) | ~v1_funct_2(E_502, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_500)) | ~v1_funct_1(E_502) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_500) | ~v2_pre_topc(B_500) | v2_struct_0(B_500) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2747])).
% 7.89/2.64  tff(c_2751, plain, (![B_500, E_502]: (v1_funct_1(k3_tmap_1('#skF_1', B_500, '#skF_1', '#skF_5', E_502)) | ~v5_pre_topc(E_502, '#skF_1', B_500) | ~m1_subset_1(E_502, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_500)))) | ~v1_funct_2(E_502, u1_struct_0('#skF_1'), u1_struct_0(B_500)) | ~v1_funct_1(E_502) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_500) | ~v2_pre_topc(B_500) | v2_struct_0(B_500) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_34, c_34, c_34, c_2749])).
% 7.89/2.64  tff(c_2752, plain, (![B_500, E_502]: (v1_funct_1(k3_tmap_1('#skF_1', B_500, '#skF_1', '#skF_5', E_502)) | ~v5_pre_topc(E_502, '#skF_1', B_500) | ~m1_subset_1(E_502, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_500)))) | ~v1_funct_2(E_502, u1_struct_0('#skF_1'), u1_struct_0(B_500)) | ~v1_funct_1(E_502) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~l1_pre_topc(B_500) | ~v2_pre_topc(B_500) | v2_struct_0(B_500))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_2751])).
% 7.89/2.64  tff(c_2869, plain, (~r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_2752])).
% 7.89/2.64  tff(c_2872, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~v1_tsep_1('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2869])).
% 7.89/2.64  tff(c_2875, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_42, c_38, c_36, c_2872])).
% 7.89/2.64  tff(c_2877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2875])).
% 7.89/2.64  tff(c_2879, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_2752])).
% 7.89/2.64  tff(c_2998, plain, (![C_524, E_525, A_522, D_526, B_523]: (v5_pre_topc(k3_tmap_1(A_522, B_523, k1_tsep_1(A_522, C_524, D_526), C_524, E_525), C_524, B_523) | ~v5_pre_topc(E_525, k1_tsep_1(A_522, C_524, D_526), B_523) | ~m1_subset_1(E_525, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_522, C_524, D_526)), u1_struct_0(B_523)))) | ~v1_funct_2(E_525, u1_struct_0(k1_tsep_1(A_522, C_524, D_526)), u1_struct_0(B_523)) | ~v1_funct_1(E_525) | ~r4_tsep_1(A_522, C_524, D_526) | ~m1_pre_topc(D_526, A_522) | v2_struct_0(D_526) | ~m1_pre_topc(C_524, A_522) | v2_struct_0(C_524) | ~l1_pre_topc(B_523) | ~v2_pre_topc(B_523) | v2_struct_0(B_523) | ~l1_pre_topc(A_522) | ~v2_pre_topc(A_522) | v2_struct_0(A_522))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_3000, plain, (![B_523, E_525]: (v5_pre_topc(k3_tmap_1('#skF_1', B_523, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_525), '#skF_4', B_523) | ~v5_pre_topc(E_525, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_523) | ~m1_subset_1(E_525, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_523)))) | ~v1_funct_2(E_525, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_523)) | ~v1_funct_1(E_525) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_523) | ~v2_pre_topc(B_523) | v2_struct_0(B_523) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2998])).
% 7.89/2.64  tff(c_3002, plain, (![B_523, E_525]: (v5_pre_topc(k3_tmap_1('#skF_1', B_523, '#skF_1', '#skF_4', E_525), '#skF_4', B_523) | ~v5_pre_topc(E_525, '#skF_1', B_523) | ~m1_subset_1(E_525, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_523)))) | ~v1_funct_2(E_525, u1_struct_0('#skF_1'), u1_struct_0(B_523)) | ~v1_funct_1(E_525) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_523) | ~v2_pre_topc(B_523) | v2_struct_0(B_523) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_2879, c_34, c_34, c_34, c_3000])).
% 7.89/2.64  tff(c_3004, plain, (![B_527, E_528]: (v5_pre_topc(k3_tmap_1('#skF_1', B_527, '#skF_1', '#skF_4', E_528), '#skF_4', B_527) | ~v5_pre_topc(E_528, '#skF_1', B_527) | ~m1_subset_1(E_528, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_527)))) | ~v1_funct_2(E_528, u1_struct_0('#skF_1'), u1_struct_0(B_527)) | ~v1_funct_1(E_528) | ~l1_pre_topc(B_527) | ~v2_pre_topc(B_527) | v2_struct_0(B_527))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_3002])).
% 7.89/2.64  tff(c_3006, plain, (v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_3004])).
% 7.89/2.64  tff(c_3009, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2683, c_2837, c_3006])).
% 7.89/2.64  tff(c_3011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2684, c_3009])).
% 7.89/2.64  tff(c_3013, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_90])).
% 7.89/2.64  tff(c_3012, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_90])).
% 7.89/2.64  tff(c_3036, plain, (![C_540, D_539, B_537, A_541, E_538]: (k3_tmap_1(A_541, B_537, C_540, D_539, E_538)=k2_partfun1(u1_struct_0(C_540), u1_struct_0(B_537), E_538, u1_struct_0(D_539)) | ~m1_pre_topc(D_539, C_540) | ~m1_subset_1(E_538, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_540), u1_struct_0(B_537)))) | ~v1_funct_2(E_538, u1_struct_0(C_540), u1_struct_0(B_537)) | ~v1_funct_1(E_538) | ~m1_pre_topc(D_539, A_541) | ~m1_pre_topc(C_540, A_541) | ~l1_pre_topc(B_537) | ~v2_pre_topc(B_537) | v2_struct_0(B_537) | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541) | v2_struct_0(A_541))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.89/2.64  tff(c_3038, plain, (![A_541, D_539]: (k3_tmap_1(A_541, '#skF_2', '#skF_1', D_539, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_539)) | ~m1_pre_topc(D_539, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_539, A_541) | ~m1_pre_topc('#skF_1', A_541) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541) | v2_struct_0(A_541))), inference(resolution, [status(thm)], [c_48, c_3036])).
% 7.89/2.64  tff(c_3041, plain, (![A_541, D_539]: (k3_tmap_1(A_541, '#skF_2', '#skF_1', D_539, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_539)) | ~m1_pre_topc(D_539, '#skF_1') | ~m1_pre_topc(D_539, A_541) | ~m1_pre_topc('#skF_1', A_541) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541) | v2_struct_0(A_541))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_3038])).
% 7.89/2.64  tff(c_3043, plain, (![A_542, D_543]: (k3_tmap_1(A_542, '#skF_2', '#skF_1', D_543, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_543)) | ~m1_pre_topc(D_543, '#skF_1') | ~m1_pre_topc(D_543, A_542) | ~m1_pre_topc('#skF_1', A_542) | ~l1_pre_topc(A_542) | ~v2_pre_topc(A_542) | v2_struct_0(A_542))), inference(negUnitSimplification, [status(thm)], [c_58, c_3041])).
% 7.89/2.64  tff(c_3047, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_3043])).
% 7.89/2.64  tff(c_3053, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_36, c_3047])).
% 7.89/2.64  tff(c_3054, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_3053])).
% 7.89/2.64  tff(c_3059, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3054])).
% 7.89/2.64  tff(c_3062, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_3059])).
% 7.89/2.64  tff(c_3066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_3062])).
% 7.89/2.64  tff(c_3067, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_3054])).
% 7.89/2.64  tff(c_3020, plain, (![A_532, B_533, C_534, D_535]: (k2_partfun1(u1_struct_0(A_532), u1_struct_0(B_533), C_534, u1_struct_0(D_535))=k2_tmap_1(A_532, B_533, C_534, D_535) | ~m1_pre_topc(D_535, A_532) | ~m1_subset_1(C_534, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_532), u1_struct_0(B_533)))) | ~v1_funct_2(C_534, u1_struct_0(A_532), u1_struct_0(B_533)) | ~v1_funct_1(C_534) | ~l1_pre_topc(B_533) | ~v2_pre_topc(B_533) | v2_struct_0(B_533) | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532) | v2_struct_0(A_532))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.89/2.64  tff(c_3022, plain, (![D_535]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_535))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_535) | ~m1_pre_topc(D_535, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_3020])).
% 7.89/2.64  tff(c_3025, plain, (![D_535]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_535))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_535) | ~m1_pre_topc(D_535, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_3022])).
% 7.89/2.64  tff(c_3026, plain, (![D_535]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_535))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_535) | ~m1_pre_topc(D_535, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_3025])).
% 7.89/2.64  tff(c_3078, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3067, c_3026])).
% 7.89/2.64  tff(c_3085, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3078])).
% 7.89/2.64  tff(c_3191, plain, (![C_551, A_549, E_552, B_550, D_553]: (v1_funct_1(k3_tmap_1(A_549, B_550, k1_tsep_1(A_549, C_551, D_553), D_553, E_552)) | ~v5_pre_topc(E_552, k1_tsep_1(A_549, C_551, D_553), B_550) | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_549, C_551, D_553)), u1_struct_0(B_550)))) | ~v1_funct_2(E_552, u1_struct_0(k1_tsep_1(A_549, C_551, D_553)), u1_struct_0(B_550)) | ~v1_funct_1(E_552) | ~r4_tsep_1(A_549, C_551, D_553) | ~m1_pre_topc(D_553, A_549) | v2_struct_0(D_553) | ~m1_pre_topc(C_551, A_549) | v2_struct_0(C_551) | ~l1_pre_topc(B_550) | ~v2_pre_topc(B_550) | v2_struct_0(B_550) | ~l1_pre_topc(A_549) | ~v2_pre_topc(A_549) | v2_struct_0(A_549))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_3193, plain, (![B_550, E_552]: (v1_funct_1(k3_tmap_1('#skF_1', B_550, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_552)) | ~v5_pre_topc(E_552, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_550) | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_550)))) | ~v1_funct_2(E_552, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_550)) | ~v1_funct_1(E_552) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_550) | ~v2_pre_topc(B_550) | v2_struct_0(B_550) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3191])).
% 7.89/2.64  tff(c_3195, plain, (![B_550, E_552]: (v1_funct_1(k3_tmap_1('#skF_1', B_550, '#skF_1', '#skF_5', E_552)) | ~v5_pre_topc(E_552, '#skF_1', B_550) | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_550)))) | ~v1_funct_2(E_552, u1_struct_0('#skF_1'), u1_struct_0(B_550)) | ~v1_funct_1(E_552) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_550) | ~v2_pre_topc(B_550) | v2_struct_0(B_550) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_34, c_34, c_34, c_3193])).
% 7.89/2.64  tff(c_3196, plain, (![B_550, E_552]: (v1_funct_1(k3_tmap_1('#skF_1', B_550, '#skF_1', '#skF_5', E_552)) | ~v5_pre_topc(E_552, '#skF_1', B_550) | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_550)))) | ~v1_funct_2(E_552, u1_struct_0('#skF_1'), u1_struct_0(B_550)) | ~v1_funct_1(E_552) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~l1_pre_topc(B_550) | ~v2_pre_topc(B_550) | v2_struct_0(B_550))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_3195])).
% 7.89/2.64  tff(c_3290, plain, (~r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_3196])).
% 7.89/2.64  tff(c_3293, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~v1_tsep_1('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3290])).
% 7.89/2.64  tff(c_3296, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_42, c_38, c_36, c_3293])).
% 7.89/2.64  tff(c_3298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_3296])).
% 7.89/2.64  tff(c_3300, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_3196])).
% 7.89/2.64  tff(c_3284, plain, (![C_558, B_557, D_560, A_556, E_559]: (v5_pre_topc(k3_tmap_1(A_556, B_557, k1_tsep_1(A_556, C_558, D_560), D_560, E_559), D_560, B_557) | ~v5_pre_topc(E_559, k1_tsep_1(A_556, C_558, D_560), B_557) | ~m1_subset_1(E_559, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_556, C_558, D_560)), u1_struct_0(B_557)))) | ~v1_funct_2(E_559, u1_struct_0(k1_tsep_1(A_556, C_558, D_560)), u1_struct_0(B_557)) | ~v1_funct_1(E_559) | ~r4_tsep_1(A_556, C_558, D_560) | ~m1_pre_topc(D_560, A_556) | v2_struct_0(D_560) | ~m1_pre_topc(C_558, A_556) | v2_struct_0(C_558) | ~l1_pre_topc(B_557) | ~v2_pre_topc(B_557) | v2_struct_0(B_557) | ~l1_pre_topc(A_556) | ~v2_pre_topc(A_556) | v2_struct_0(A_556))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_3286, plain, (![B_557, E_559]: (v5_pre_topc(k3_tmap_1('#skF_1', B_557, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_559), '#skF_5', B_557) | ~v5_pre_topc(E_559, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_557) | ~m1_subset_1(E_559, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_557)))) | ~v1_funct_2(E_559, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_557)) | ~v1_funct_1(E_559) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_557) | ~v2_pre_topc(B_557) | v2_struct_0(B_557) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3284])).
% 7.89/2.64  tff(c_3288, plain, (![B_557, E_559]: (v5_pre_topc(k3_tmap_1('#skF_1', B_557, '#skF_1', '#skF_5', E_559), '#skF_5', B_557) | ~v5_pre_topc(E_559, '#skF_1', B_557) | ~m1_subset_1(E_559, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_557)))) | ~v1_funct_2(E_559, u1_struct_0('#skF_1'), u1_struct_0(B_557)) | ~v1_funct_1(E_559) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_557) | ~v2_pre_topc(B_557) | v2_struct_0(B_557) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_34, c_34, c_34, c_3286])).
% 7.89/2.64  tff(c_3289, plain, (![B_557, E_559]: (v5_pre_topc(k3_tmap_1('#skF_1', B_557, '#skF_1', '#skF_5', E_559), '#skF_5', B_557) | ~v5_pre_topc(E_559, '#skF_1', B_557) | ~m1_subset_1(E_559, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_557)))) | ~v1_funct_2(E_559, u1_struct_0('#skF_1'), u1_struct_0(B_557)) | ~v1_funct_1(E_559) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~l1_pre_topc(B_557) | ~v2_pre_topc(B_557) | v2_struct_0(B_557))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_3288])).
% 7.89/2.64  tff(c_3321, plain, (![B_565, E_566]: (v5_pre_topc(k3_tmap_1('#skF_1', B_565, '#skF_1', '#skF_5', E_566), '#skF_5', B_565) | ~v5_pre_topc(E_566, '#skF_1', B_565) | ~m1_subset_1(E_566, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_565)))) | ~v1_funct_2(E_566, u1_struct_0('#skF_1'), u1_struct_0(B_565)) | ~v1_funct_1(E_566) | ~l1_pre_topc(B_565) | ~v2_pre_topc(B_565) | v2_struct_0(B_565))), inference(demodulation, [status(thm), theory('equality')], [c_3300, c_3289])).
% 7.89/2.64  tff(c_3323, plain, (v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), '#skF_5', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_3321])).
% 7.89/2.64  tff(c_3326, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_3012, c_3085, c_3323])).
% 7.89/2.64  tff(c_3328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_3013, c_3326])).
% 7.89/2.64  tff(c_3330, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_110])).
% 7.89/2.64  tff(c_3329, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_110])).
% 7.89/2.64  tff(c_3354, plain, (![E_576, A_579, B_575, C_578, D_577]: (k3_tmap_1(A_579, B_575, C_578, D_577, E_576)=k2_partfun1(u1_struct_0(C_578), u1_struct_0(B_575), E_576, u1_struct_0(D_577)) | ~m1_pre_topc(D_577, C_578) | ~m1_subset_1(E_576, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_578), u1_struct_0(B_575)))) | ~v1_funct_2(E_576, u1_struct_0(C_578), u1_struct_0(B_575)) | ~v1_funct_1(E_576) | ~m1_pre_topc(D_577, A_579) | ~m1_pre_topc(C_578, A_579) | ~l1_pre_topc(B_575) | ~v2_pre_topc(B_575) | v2_struct_0(B_575) | ~l1_pre_topc(A_579) | ~v2_pre_topc(A_579) | v2_struct_0(A_579))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.89/2.64  tff(c_3356, plain, (![A_579, D_577]: (k3_tmap_1(A_579, '#skF_2', '#skF_1', D_577, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_577)) | ~m1_pre_topc(D_577, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_577, A_579) | ~m1_pre_topc('#skF_1', A_579) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_579) | ~v2_pre_topc(A_579) | v2_struct_0(A_579))), inference(resolution, [status(thm)], [c_48, c_3354])).
% 7.89/2.64  tff(c_3359, plain, (![A_579, D_577]: (k3_tmap_1(A_579, '#skF_2', '#skF_1', D_577, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_577)) | ~m1_pre_topc(D_577, '#skF_1') | ~m1_pre_topc(D_577, A_579) | ~m1_pre_topc('#skF_1', A_579) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_579) | ~v2_pre_topc(A_579) | v2_struct_0(A_579))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_3356])).
% 7.89/2.64  tff(c_3361, plain, (![A_580, D_581]: (k3_tmap_1(A_580, '#skF_2', '#skF_1', D_581, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_581)) | ~m1_pre_topc(D_581, '#skF_1') | ~m1_pre_topc(D_581, A_580) | ~m1_pre_topc('#skF_1', A_580) | ~l1_pre_topc(A_580) | ~v2_pre_topc(A_580) | v2_struct_0(A_580))), inference(negUnitSimplification, [status(thm)], [c_58, c_3359])).
% 7.89/2.64  tff(c_3365, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_3361])).
% 7.89/2.64  tff(c_3371, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_36, c_3365])).
% 7.89/2.64  tff(c_3372, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_3371])).
% 7.89/2.64  tff(c_3383, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3372])).
% 7.89/2.64  tff(c_3386, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_3383])).
% 7.89/2.64  tff(c_3390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_3386])).
% 7.89/2.64  tff(c_3391, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_3372])).
% 7.89/2.64  tff(c_3338, plain, (![A_570, B_571, C_572, D_573]: (k2_partfun1(u1_struct_0(A_570), u1_struct_0(B_571), C_572, u1_struct_0(D_573))=k2_tmap_1(A_570, B_571, C_572, D_573) | ~m1_pre_topc(D_573, A_570) | ~m1_subset_1(C_572, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_570), u1_struct_0(B_571)))) | ~v1_funct_2(C_572, u1_struct_0(A_570), u1_struct_0(B_571)) | ~v1_funct_1(C_572) | ~l1_pre_topc(B_571) | ~v2_pre_topc(B_571) | v2_struct_0(B_571) | ~l1_pre_topc(A_570) | ~v2_pre_topc(A_570) | v2_struct_0(A_570))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.89/2.64  tff(c_3340, plain, (![D_573]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_573))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_573) | ~m1_pre_topc(D_573, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_3338])).
% 7.89/2.64  tff(c_3343, plain, (![D_573]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_573))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_573) | ~m1_pre_topc(D_573, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_3340])).
% 7.89/2.64  tff(c_3344, plain, (![D_573]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_573))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_573) | ~m1_pre_topc(D_573, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_3343])).
% 7.89/2.64  tff(c_3438, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3391, c_3344])).
% 7.89/2.64  tff(c_3445, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3438])).
% 7.89/2.64  tff(c_3377, plain, (![C_584, D_586, E_585, A_582, B_583]: (v1_funct_1(k3_tmap_1(A_582, B_583, k1_tsep_1(A_582, C_584, D_586), D_586, E_585)) | ~v5_pre_topc(E_585, k1_tsep_1(A_582, C_584, D_586), B_583) | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_582, C_584, D_586)), u1_struct_0(B_583)))) | ~v1_funct_2(E_585, u1_struct_0(k1_tsep_1(A_582, C_584, D_586)), u1_struct_0(B_583)) | ~v1_funct_1(E_585) | ~r4_tsep_1(A_582, C_584, D_586) | ~m1_pre_topc(D_586, A_582) | v2_struct_0(D_586) | ~m1_pre_topc(C_584, A_582) | v2_struct_0(C_584) | ~l1_pre_topc(B_583) | ~v2_pre_topc(B_583) | v2_struct_0(B_583) | ~l1_pre_topc(A_582) | ~v2_pre_topc(A_582) | v2_struct_0(A_582))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.64  tff(c_3379, plain, (![B_583, E_585]: (v1_funct_1(k3_tmap_1('#skF_1', B_583, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_585)) | ~v5_pre_topc(E_585, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_583) | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_583)))) | ~v1_funct_2(E_585, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_583)) | ~v1_funct_1(E_585) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_583) | ~v2_pre_topc(B_583) | v2_struct_0(B_583) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3377])).
% 7.89/2.64  tff(c_3381, plain, (![B_583, E_585]: (v1_funct_1(k3_tmap_1('#skF_1', B_583, '#skF_1', '#skF_5', E_585)) | ~v5_pre_topc(E_585, '#skF_1', B_583) | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_583)))) | ~v1_funct_2(E_585, u1_struct_0('#skF_1'), u1_struct_0(B_583)) | ~v1_funct_1(E_585) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_583) | ~v2_pre_topc(B_583) | v2_struct_0(B_583) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_34, c_34, c_34, c_3379])).
% 7.89/2.64  tff(c_3382, plain, (![B_583, E_585]: (v1_funct_1(k3_tmap_1('#skF_1', B_583, '#skF_1', '#skF_5', E_585)) | ~v5_pre_topc(E_585, '#skF_1', B_583) | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_583)))) | ~v1_funct_2(E_585, u1_struct_0('#skF_1'), u1_struct_0(B_583)) | ~v1_funct_1(E_585) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~l1_pre_topc(B_583) | ~v2_pre_topc(B_583) | v2_struct_0(B_583))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_3381])).
% 7.89/2.64  tff(c_3493, plain, (~r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_3382])).
% 7.89/2.64  tff(c_3496, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~v1_tsep_1('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3493])).
% 7.89/2.64  tff(c_3499, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_42, c_38, c_36, c_3496])).
% 7.89/2.64  tff(c_3501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_3499])).
% 7.89/2.65  tff(c_3625, plain, (![B_604, E_605]: (v1_funct_1(k3_tmap_1('#skF_1', B_604, '#skF_1', '#skF_5', E_605)) | ~v5_pre_topc(E_605, '#skF_1', B_604) | ~m1_subset_1(E_605, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_604)))) | ~v1_funct_2(E_605, u1_struct_0('#skF_1'), u1_struct_0(B_604)) | ~v1_funct_1(E_605) | ~l1_pre_topc(B_604) | ~v2_pre_topc(B_604) | v2_struct_0(B_604))), inference(splitRight, [status(thm)], [c_3382])).
% 7.89/2.65  tff(c_3628, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_3625])).
% 7.89/2.65  tff(c_3631, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_3329, c_3445, c_3628])).
% 7.89/2.65  tff(c_3633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_3330, c_3631])).
% 7.89/2.65  tff(c_3635, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_150])).
% 7.89/2.65  tff(c_3634, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_150])).
% 7.89/2.65  tff(c_3662, plain, (![E_615, D_616, C_617, A_618, B_614]: (k3_tmap_1(A_618, B_614, C_617, D_616, E_615)=k2_partfun1(u1_struct_0(C_617), u1_struct_0(B_614), E_615, u1_struct_0(D_616)) | ~m1_pre_topc(D_616, C_617) | ~m1_subset_1(E_615, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_617), u1_struct_0(B_614)))) | ~v1_funct_2(E_615, u1_struct_0(C_617), u1_struct_0(B_614)) | ~v1_funct_1(E_615) | ~m1_pre_topc(D_616, A_618) | ~m1_pre_topc(C_617, A_618) | ~l1_pre_topc(B_614) | ~v2_pre_topc(B_614) | v2_struct_0(B_614) | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.89/2.65  tff(c_3664, plain, (![A_618, D_616]: (k3_tmap_1(A_618, '#skF_2', '#skF_1', D_616, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_616)) | ~m1_pre_topc(D_616, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_616, A_618) | ~m1_pre_topc('#skF_1', A_618) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(resolution, [status(thm)], [c_48, c_3662])).
% 7.89/2.65  tff(c_3667, plain, (![A_618, D_616]: (k3_tmap_1(A_618, '#skF_2', '#skF_1', D_616, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_616)) | ~m1_pre_topc(D_616, '#skF_1') | ~m1_pre_topc(D_616, A_618) | ~m1_pre_topc('#skF_1', A_618) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_3664])).
% 7.89/2.65  tff(c_3669, plain, (![A_619, D_620]: (k3_tmap_1(A_619, '#skF_2', '#skF_1', D_620, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_620)) | ~m1_pre_topc(D_620, '#skF_1') | ~m1_pre_topc(D_620, A_619) | ~m1_pre_topc('#skF_1', A_619) | ~l1_pre_topc(A_619) | ~v2_pre_topc(A_619) | v2_struct_0(A_619))), inference(negUnitSimplification, [status(thm)], [c_58, c_3667])).
% 7.89/2.65  tff(c_3673, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_3669])).
% 7.89/2.65  tff(c_3679, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_36, c_3673])).
% 7.89/2.65  tff(c_3680, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_3679])).
% 7.89/2.65  tff(c_3685, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3680])).
% 7.89/2.65  tff(c_3688, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_3685])).
% 7.89/2.65  tff(c_3692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_3688])).
% 7.89/2.65  tff(c_3694, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_3680])).
% 7.89/2.65  tff(c_3675, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_3669])).
% 7.89/2.65  tff(c_3683, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_3675])).
% 7.89/2.65  tff(c_3684, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_3683])).
% 7.89/2.65  tff(c_3780, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3694, c_3684])).
% 7.89/2.65  tff(c_3644, plain, (![A_609, B_610, C_611, D_612]: (k2_partfun1(u1_struct_0(A_609), u1_struct_0(B_610), C_611, u1_struct_0(D_612))=k2_tmap_1(A_609, B_610, C_611, D_612) | ~m1_pre_topc(D_612, A_609) | ~m1_subset_1(C_611, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_609), u1_struct_0(B_610)))) | ~v1_funct_2(C_611, u1_struct_0(A_609), u1_struct_0(B_610)) | ~v1_funct_1(C_611) | ~l1_pre_topc(B_610) | ~v2_pre_topc(B_610) | v2_struct_0(B_610) | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.89/2.65  tff(c_3646, plain, (![D_612]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_612))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_612) | ~m1_pre_topc(D_612, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_3644])).
% 7.89/2.65  tff(c_3649, plain, (![D_612]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_612))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_612) | ~m1_pre_topc(D_612, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_3646])).
% 7.89/2.65  tff(c_3650, plain, (![D_612]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_612))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_612) | ~m1_pre_topc(D_612, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_3649])).
% 7.89/2.65  tff(c_3784, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3780, c_3650])).
% 7.89/2.65  tff(c_3791, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3784])).
% 7.89/2.65  tff(c_3701, plain, (![C_623, A_621, B_622, E_624, D_625]: (v1_funct_1(k3_tmap_1(A_621, B_622, k1_tsep_1(A_621, C_623, D_625), C_623, E_624)) | ~v5_pre_topc(E_624, k1_tsep_1(A_621, C_623, D_625), B_622) | ~m1_subset_1(E_624, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_621, C_623, D_625)), u1_struct_0(B_622)))) | ~v1_funct_2(E_624, u1_struct_0(k1_tsep_1(A_621, C_623, D_625)), u1_struct_0(B_622)) | ~v1_funct_1(E_624) | ~r4_tsep_1(A_621, C_623, D_625) | ~m1_pre_topc(D_625, A_621) | v2_struct_0(D_625) | ~m1_pre_topc(C_623, A_621) | v2_struct_0(C_623) | ~l1_pre_topc(B_622) | ~v2_pre_topc(B_622) | v2_struct_0(B_622) | ~l1_pre_topc(A_621) | ~v2_pre_topc(A_621) | v2_struct_0(A_621))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.89/2.65  tff(c_3703, plain, (![B_622, E_624]: (v1_funct_1(k3_tmap_1('#skF_1', B_622, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_624)) | ~v5_pre_topc(E_624, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_622) | ~m1_subset_1(E_624, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_622)))) | ~v1_funct_2(E_624, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_622)) | ~v1_funct_1(E_624) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_622) | ~v2_pre_topc(B_622) | v2_struct_0(B_622) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3701])).
% 7.89/2.65  tff(c_3705, plain, (![B_622, E_624]: (v1_funct_1(k3_tmap_1('#skF_1', B_622, '#skF_1', '#skF_4', E_624)) | ~v5_pre_topc(E_624, '#skF_1', B_622) | ~m1_subset_1(E_624, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_622)))) | ~v1_funct_2(E_624, u1_struct_0('#skF_1'), u1_struct_0(B_622)) | ~v1_funct_1(E_624) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_622) | ~v2_pre_topc(B_622) | v2_struct_0(B_622) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_42, c_36, c_34, c_34, c_34, c_3703])).
% 7.89/2.65  tff(c_3706, plain, (![B_622, E_624]: (v1_funct_1(k3_tmap_1('#skF_1', B_622, '#skF_1', '#skF_4', E_624)) | ~v5_pre_topc(E_624, '#skF_1', B_622) | ~m1_subset_1(E_624, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_622)))) | ~v1_funct_2(E_624, u1_struct_0('#skF_1'), u1_struct_0(B_622)) | ~v1_funct_1(E_624) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~l1_pre_topc(B_622) | ~v2_pre_topc(B_622) | v2_struct_0(B_622))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_40, c_3705])).
% 7.89/2.65  tff(c_3823, plain, (~r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_3706])).
% 7.89/2.65  tff(c_3826, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~v1_tsep_1('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3823])).
% 7.89/2.65  tff(c_3829, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_42, c_38, c_36, c_3826])).
% 7.89/2.65  tff(c_3831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_3829])).
% 7.89/2.65  tff(c_3927, plain, (![B_638, E_639]: (v1_funct_1(k3_tmap_1('#skF_1', B_638, '#skF_1', '#skF_4', E_639)) | ~v5_pre_topc(E_639, '#skF_1', B_638) | ~m1_subset_1(E_639, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_638)))) | ~v1_funct_2(E_639, u1_struct_0('#skF_1'), u1_struct_0(B_638)) | ~v1_funct_1(E_639) | ~l1_pre_topc(B_638) | ~v2_pre_topc(B_638) | v2_struct_0(B_638))), inference(splitRight, [status(thm)], [c_3706])).
% 7.89/2.65  tff(c_3930, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_3927])).
% 7.89/2.65  tff(c_3933, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_3634, c_3791, c_3930])).
% 7.89/2.65  tff(c_3935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_3635, c_3933])).
% 7.89/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.89/2.65  
% 7.89/2.65  Inference rules
% 7.89/2.65  ----------------------
% 7.89/2.65  #Ref     : 0
% 7.89/2.65  #Sup     : 749
% 7.89/2.65  #Fact    : 0
% 7.89/2.65  #Define  : 0
% 7.89/2.65  #Split   : 47
% 7.89/2.65  #Chain   : 0
% 7.89/2.65  #Close   : 0
% 7.89/2.65  
% 7.89/2.65  Ordering : KBO
% 7.89/2.65  
% 7.89/2.65  Simplification rules
% 7.89/2.65  ----------------------
% 7.89/2.65  #Subsume      : 102
% 7.89/2.65  #Demod        : 1450
% 7.89/2.65  #Tautology    : 444
% 7.89/2.65  #SimpNegUnit  : 287
% 7.89/2.65  #BackRed      : 27
% 7.89/2.65  
% 7.89/2.65  #Partial instantiations: 0
% 7.89/2.65  #Strategies tried      : 1
% 7.89/2.65  
% 7.89/2.65  Timing (in seconds)
% 7.89/2.65  ----------------------
% 7.89/2.65  Preprocessing        : 0.41
% 7.89/2.65  Parsing              : 0.19
% 7.89/2.65  CNF conversion       : 0.06
% 7.89/2.65  Main loop            : 1.27
% 7.89/2.65  Inferencing          : 0.44
% 7.89/2.65  Reduction            : 0.42
% 7.89/2.65  Demodulation         : 0.30
% 7.89/2.65  BG Simplification    : 0.07
% 7.89/2.65  Subsumption          : 0.29
% 7.89/2.65  Abstraction          : 0.07
% 7.89/2.65  MUC search           : 0.00
% 7.89/2.65  Cooper               : 0.00
% 7.89/2.65  Total                : 1.87
% 7.89/2.65  Index Insertion      : 0.00
% 7.89/2.65  Index Deletion       : 0.00
% 7.89/2.65  Index Matching       : 0.00
% 7.89/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
