%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:07 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.53s
% Verified   : 
% Statistics : Number of formulae       :  303 (1759 expanded)
%              Number of leaves         :   30 ( 735 expanded)
%              Depth                    :   12
%              Number of atoms          : 1665 (21307 expanded)
%              Number of equality atoms :  126 ( 952 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(f_229,negated_conjecture,(
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

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

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

tff(f_166,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_150,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_190,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_140,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_193,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_130,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_192,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_120,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_196,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_110,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_189,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_100,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_194,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_90,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_191,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_80,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_195,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

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
    inference(cnfTransformation,[status(thm)],[f_229])).

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

tff(c_654,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_193,c_192,c_196,c_189,c_194,c_191,c_195,c_184])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_40,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_38,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_211,plain,(
    ! [A_113,B_114,C_115] :
      ( m1_pre_topc(k1_tsep_1(A_113,B_114,C_115),A_113)
      | ~ m1_pre_topc(C_115,A_113)
      | v2_struct_0(C_115)
      | ~ m1_pre_topc(B_114,A_113)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_214,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_211])).

tff(c_216,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44,c_40,c_214])).

tff(c_217,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_216])).

tff(c_248,plain,(
    ! [B_121,E_122,D_123,A_125,C_124] :
      ( k3_tmap_1(A_125,B_121,C_124,D_123,E_122) = k2_partfun1(u1_struct_0(C_124),u1_struct_0(B_121),E_122,u1_struct_0(D_123))
      | ~ m1_pre_topc(D_123,C_124)
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_124),u1_struct_0(B_121))))
      | ~ v1_funct_2(E_122,u1_struct_0(C_124),u1_struct_0(B_121))
      | ~ v1_funct_1(E_122)
      | ~ m1_pre_topc(D_123,A_125)
      | ~ m1_pre_topc(C_124,A_125)
      | ~ l1_pre_topc(B_121)
      | ~ v2_pre_topc(B_121)
      | v2_struct_0(B_121)
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_254,plain,(
    ! [A_125,D_123] :
      ( k3_tmap_1(A_125,'#skF_2','#skF_1',D_123,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_123))
      | ~ m1_pre_topc(D_123,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_123,A_125)
      | ~ m1_pre_topc('#skF_1',A_125)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_48,c_248])).

tff(c_265,plain,(
    ! [A_125,D_123] :
      ( k3_tmap_1(A_125,'#skF_2','#skF_1',D_123,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_123))
      | ~ m1_pre_topc(D_123,'#skF_1')
      | ~ m1_pre_topc(D_123,A_125)
      | ~ m1_pre_topc('#skF_1',A_125)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_254])).

tff(c_267,plain,(
    ! [A_126,D_127] :
      ( k3_tmap_1(A_126,'#skF_2','#skF_1',D_127,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_127))
      | ~ m1_pre_topc(D_127,'#skF_1')
      | ~ m1_pre_topc(D_127,A_126)
      | ~ m1_pre_topc('#skF_1',A_126)
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_265])).

tff(c_273,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_267])).

tff(c_283,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_217,c_44,c_273])).

tff(c_284,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_283])).

tff(c_218,plain,(
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

tff(c_224,plain,(
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
    inference(resolution,[status(thm)],[c_48,c_218])).

tff(c_235,plain,(
    ! [D_119] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_119)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_119)
      | ~ m1_pre_topc(D_119,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_224])).

tff(c_236,plain,(
    ! [D_119] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_119)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_119)
      | ~ m1_pre_topc(D_119,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_235])).

tff(c_370,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_236])).

tff(c_377,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_370])).

tff(c_275,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_267])).

tff(c_287,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_217,c_40,c_275])).

tff(c_288,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_287])).

tff(c_334,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_236])).

tff(c_341,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_334])).

tff(c_36,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_852,plain,(
    ! [B_212,C_211,D_210,E_209,A_208] :
      ( v5_pre_topc(E_209,k1_tsep_1(A_208,C_211,D_210),B_212)
      | ~ m1_subset_1(k3_tmap_1(A_208,B_212,k1_tsep_1(A_208,C_211,D_210),D_210,E_209),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_210),u1_struct_0(B_212))))
      | ~ v5_pre_topc(k3_tmap_1(A_208,B_212,k1_tsep_1(A_208,C_211,D_210),D_210,E_209),D_210,B_212)
      | ~ v1_funct_2(k3_tmap_1(A_208,B_212,k1_tsep_1(A_208,C_211,D_210),D_210,E_209),u1_struct_0(D_210),u1_struct_0(B_212))
      | ~ v1_funct_1(k3_tmap_1(A_208,B_212,k1_tsep_1(A_208,C_211,D_210),D_210,E_209))
      | ~ m1_subset_1(k3_tmap_1(A_208,B_212,k1_tsep_1(A_208,C_211,D_210),C_211,E_209),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_211),u1_struct_0(B_212))))
      | ~ v5_pre_topc(k3_tmap_1(A_208,B_212,k1_tsep_1(A_208,C_211,D_210),C_211,E_209),C_211,B_212)
      | ~ v1_funct_2(k3_tmap_1(A_208,B_212,k1_tsep_1(A_208,C_211,D_210),C_211,E_209),u1_struct_0(C_211),u1_struct_0(B_212))
      | ~ v1_funct_1(k3_tmap_1(A_208,B_212,k1_tsep_1(A_208,C_211,D_210),C_211,E_209))
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_208,C_211,D_210)),u1_struct_0(B_212))))
      | ~ v1_funct_2(E_209,u1_struct_0(k1_tsep_1(A_208,C_211,D_210)),u1_struct_0(B_212))
      | ~ v1_funct_1(E_209)
      | ~ r4_tsep_1(A_208,C_211,D_210)
      | ~ m1_pre_topc(D_210,A_208)
      | v2_struct_0(D_210)
      | ~ m1_pre_topc(C_211,A_208)
      | v2_struct_0(C_211)
      | ~ l1_pre_topc(B_212)
      | ~ v2_pre_topc(B_212)
      | v2_struct_0(B_212)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_859,plain,(
    ! [E_209,B_212] :
      ( v5_pre_topc(E_209,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_212)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_212,'#skF_1','#skF_5',E_209),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_212))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_212,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_209),'#skF_5',B_212)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_212,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_209),u1_struct_0('#skF_5'),u1_struct_0(B_212))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_212,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_209))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_212,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_209),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_212))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_212,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_209),'#skF_4',B_212)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_212,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_209),u1_struct_0('#skF_4'),u1_struct_0(B_212))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_212,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_209))
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_212))))
      | ~ v1_funct_2(E_209,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_212))
      | ~ v1_funct_1(E_209)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_212)
      | ~ v2_pre_topc(B_212)
      | v2_struct_0(B_212)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_852])).

tff(c_863,plain,(
    ! [E_209,B_212] :
      ( v5_pre_topc(E_209,'#skF_1',B_212)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_212,'#skF_1','#skF_5',E_209),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_212))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_212,'#skF_1','#skF_5',E_209),'#skF_5',B_212)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_212,'#skF_1','#skF_5',E_209),u1_struct_0('#skF_5'),u1_struct_0(B_212))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_212,'#skF_1','#skF_5',E_209))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_212,'#skF_1','#skF_4',E_209),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_212))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_212,'#skF_1','#skF_4',E_209),'#skF_4',B_212)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_212,'#skF_1','#skF_4',E_209),u1_struct_0('#skF_4'),u1_struct_0(B_212))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_212,'#skF_1','#skF_4',E_209))
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_212))))
      | ~ v1_funct_2(E_209,u1_struct_0('#skF_1'),u1_struct_0(B_212))
      | ~ v1_funct_1(E_209)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_212)
      | ~ v2_pre_topc(B_212)
      | v2_struct_0(B_212)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_40,c_36,c_38,c_38,c_38,c_38,c_38,c_38,c_38,c_38,c_38,c_38,c_859])).

tff(c_888,plain,(
    ! [E_233,B_234] :
      ( v5_pre_topc(E_233,'#skF_1',B_234)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_234,'#skF_1','#skF_5',E_233),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_234))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_234,'#skF_1','#skF_5',E_233),'#skF_5',B_234)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_234,'#skF_1','#skF_5',E_233),u1_struct_0('#skF_5'),u1_struct_0(B_234))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_234,'#skF_1','#skF_5',E_233))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_234,'#skF_1','#skF_4',E_233),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_234))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_234,'#skF_1','#skF_4',E_233),'#skF_4',B_234)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_234,'#skF_1','#skF_4',E_233),u1_struct_0('#skF_4'),u1_struct_0(B_234))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_234,'#skF_1','#skF_4',E_233))
      | ~ m1_subset_1(E_233,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_234))))
      | ~ v1_funct_2(E_233,u1_struct_0('#skF_1'),u1_struct_0(B_234))
      | ~ v1_funct_1(E_233)
      | ~ l1_pre_topc(B_234)
      | ~ v2_pre_topc(B_234)
      | v2_struct_0(B_234) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_863])).

tff(c_894,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_341,c_888])).

tff(c_897,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_190,c_377,c_193,c_377,c_192,c_377,c_196,c_377,c_189,c_341,c_194,c_341,c_191,c_341,c_195,c_894])).

tff(c_899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_654,c_897])).

tff(c_901,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_900,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_925,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( k2_partfun1(u1_struct_0(A_244),u1_struct_0(B_245),C_246,u1_struct_0(D_247)) = k2_tmap_1(A_244,B_245,C_246,D_247)
      | ~ m1_pre_topc(D_247,A_244)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_244),u1_struct_0(B_245))))
      | ~ v1_funct_2(C_246,u1_struct_0(A_244),u1_struct_0(B_245))
      | ~ v1_funct_1(C_246)
      | ~ l1_pre_topc(B_245)
      | ~ v2_pre_topc(B_245)
      | v2_struct_0(B_245)
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_929,plain,(
    ! [D_247] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_247)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_247)
      | ~ m1_pre_topc(D_247,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_925])).

tff(c_936,plain,(
    ! [D_247] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_247)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_247)
      | ~ m1_pre_topc(D_247,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_929])).

tff(c_937,plain,(
    ! [D_247] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_247)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_247)
      | ~ m1_pre_topc(D_247,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_936])).

tff(c_916,plain,(
    ! [A_241,B_242,C_243] :
      ( m1_pre_topc(k1_tsep_1(A_241,B_242,C_243),A_241)
      | ~ m1_pre_topc(C_243,A_241)
      | v2_struct_0(C_243)
      | ~ m1_pre_topc(B_242,A_241)
      | v2_struct_0(B_242)
      | ~ l1_pre_topc(A_241)
      | v2_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_919,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_916])).

tff(c_921,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44,c_40,c_919])).

tff(c_922,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_921])).

tff(c_948,plain,(
    ! [C_252,B_249,D_251,A_253,E_250] :
      ( k3_tmap_1(A_253,B_249,C_252,D_251,E_250) = k2_partfun1(u1_struct_0(C_252),u1_struct_0(B_249),E_250,u1_struct_0(D_251))
      | ~ m1_pre_topc(D_251,C_252)
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_252),u1_struct_0(B_249))))
      | ~ v1_funct_2(E_250,u1_struct_0(C_252),u1_struct_0(B_249))
      | ~ v1_funct_1(E_250)
      | ~ m1_pre_topc(D_251,A_253)
      | ~ m1_pre_topc(C_252,A_253)
      | ~ l1_pre_topc(B_249)
      | ~ v2_pre_topc(B_249)
      | v2_struct_0(B_249)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_952,plain,(
    ! [A_253,D_251] :
      ( k3_tmap_1(A_253,'#skF_2','#skF_1',D_251,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_251))
      | ~ m1_pre_topc(D_251,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_251,A_253)
      | ~ m1_pre_topc('#skF_1',A_253)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(resolution,[status(thm)],[c_48,c_948])).

tff(c_959,plain,(
    ! [A_253,D_251] :
      ( k3_tmap_1(A_253,'#skF_2','#skF_1',D_251,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_251))
      | ~ m1_pre_topc(D_251,'#skF_1')
      | ~ m1_pre_topc(D_251,A_253)
      | ~ m1_pre_topc('#skF_1',A_253)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_952])).

tff(c_967,plain,(
    ! [A_259,D_260] :
      ( k3_tmap_1(A_259,'#skF_2','#skF_1',D_260,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_260))
      | ~ m1_pre_topc(D_260,'#skF_1')
      | ~ m1_pre_topc(D_260,A_259)
      | ~ m1_pre_topc('#skF_1',A_259)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_959])).

tff(c_973,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_967])).

tff(c_983,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_922,c_44,c_973])).

tff(c_984,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_983])).

tff(c_1015,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_937,c_984])).

tff(c_1021,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1015])).

tff(c_1384,plain,(
    ! [C_323,D_322,A_320,B_324,E_321] :
      ( m1_subset_1(k3_tmap_1(A_320,B_324,k1_tsep_1(A_320,C_323,D_322),C_323,E_321),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_323),u1_struct_0(B_324))))
      | ~ v5_pre_topc(E_321,k1_tsep_1(A_320,C_323,D_322),B_324)
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_320,C_323,D_322)),u1_struct_0(B_324))))
      | ~ v1_funct_2(E_321,u1_struct_0(k1_tsep_1(A_320,C_323,D_322)),u1_struct_0(B_324))
      | ~ v1_funct_1(E_321)
      | ~ r4_tsep_1(A_320,C_323,D_322)
      | ~ m1_pre_topc(D_322,A_320)
      | v2_struct_0(D_322)
      | ~ m1_pre_topc(C_323,A_320)
      | v2_struct_0(C_323)
      | ~ l1_pre_topc(B_324)
      | ~ v2_pre_topc(B_324)
      | v2_struct_0(B_324)
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320)
      | v2_struct_0(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1429,plain,(
    ! [B_324,E_321] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_324,'#skF_1','#skF_4',E_321),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_324))))
      | ~ v5_pre_topc(E_321,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_324)
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_324))))
      | ~ v1_funct_2(E_321,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_324))
      | ~ v1_funct_1(E_321)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_324)
      | ~ v2_pre_topc(B_324)
      | v2_struct_0(B_324)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1384])).

tff(c_1457,plain,(
    ! [B_324,E_321] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_324,'#skF_1','#skF_4',E_321),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_324))))
      | ~ v5_pre_topc(E_321,'#skF_1',B_324)
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_324))))
      | ~ v1_funct_2(E_321,u1_struct_0('#skF_1'),u1_struct_0(B_324))
      | ~ v1_funct_1(E_321)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_324)
      | ~ v2_pre_topc(B_324)
      | v2_struct_0(B_324)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_40,c_36,c_38,c_38,c_38,c_1429])).

tff(c_1459,plain,(
    ! [B_325,E_326] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_325,'#skF_1','#skF_4',E_326),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_325))))
      | ~ v5_pre_topc(E_326,'#skF_1',B_325)
      | ~ m1_subset_1(E_326,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_325))))
      | ~ v1_funct_2(E_326,u1_struct_0('#skF_1'),u1_struct_0(B_325))
      | ~ v1_funct_1(E_326)
      | ~ l1_pre_topc(B_325)
      | ~ v2_pre_topc(B_325)
      | v2_struct_0(B_325) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_1457])).

tff(c_1466,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_1459])).

tff(c_1472,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_900,c_1466])).

tff(c_1474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_901,c_1472])).

tff(c_1476,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1475,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1492,plain,(
    ! [A_333,B_334,C_335] :
      ( m1_pre_topc(k1_tsep_1(A_333,B_334,C_335),A_333)
      | ~ m1_pre_topc(C_335,A_333)
      | v2_struct_0(C_335)
      | ~ m1_pre_topc(B_334,A_333)
      | v2_struct_0(B_334)
      | ~ l1_pre_topc(A_333)
      | v2_struct_0(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1495,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1492])).

tff(c_1497,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44,c_40,c_1495])).

tff(c_1498,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_1497])).

tff(c_1515,plain,(
    ! [B_341,E_342,D_343,C_344,A_345] :
      ( k3_tmap_1(A_345,B_341,C_344,D_343,E_342) = k2_partfun1(u1_struct_0(C_344),u1_struct_0(B_341),E_342,u1_struct_0(D_343))
      | ~ m1_pre_topc(D_343,C_344)
      | ~ m1_subset_1(E_342,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_344),u1_struct_0(B_341))))
      | ~ v1_funct_2(E_342,u1_struct_0(C_344),u1_struct_0(B_341))
      | ~ v1_funct_1(E_342)
      | ~ m1_pre_topc(D_343,A_345)
      | ~ m1_pre_topc(C_344,A_345)
      | ~ l1_pre_topc(B_341)
      | ~ v2_pre_topc(B_341)
      | v2_struct_0(B_341)
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1517,plain,(
    ! [A_345,D_343] :
      ( k3_tmap_1(A_345,'#skF_2','#skF_1',D_343,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_343))
      | ~ m1_pre_topc(D_343,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_343,A_345)
      | ~ m1_pre_topc('#skF_1',A_345)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(resolution,[status(thm)],[c_48,c_1515])).

tff(c_1520,plain,(
    ! [A_345,D_343] :
      ( k3_tmap_1(A_345,'#skF_2','#skF_1',D_343,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_343))
      | ~ m1_pre_topc(D_343,'#skF_1')
      | ~ m1_pre_topc(D_343,A_345)
      | ~ m1_pre_topc('#skF_1',A_345)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_1517])).

tff(c_1522,plain,(
    ! [A_346,D_347] :
      ( k3_tmap_1(A_346,'#skF_2','#skF_1',D_347,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_347))
      | ~ m1_pre_topc(D_347,'#skF_1')
      | ~ m1_pre_topc(D_347,A_346)
      | ~ m1_pre_topc('#skF_1',A_346)
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1520])).

tff(c_1530,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1522])).

tff(c_1542,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1498,c_40,c_1530])).

tff(c_1543,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1542])).

tff(c_1499,plain,(
    ! [A_336,B_337,C_338,D_339] :
      ( k2_partfun1(u1_struct_0(A_336),u1_struct_0(B_337),C_338,u1_struct_0(D_339)) = k2_tmap_1(A_336,B_337,C_338,D_339)
      | ~ m1_pre_topc(D_339,A_336)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_336),u1_struct_0(B_337))))
      | ~ v1_funct_2(C_338,u1_struct_0(A_336),u1_struct_0(B_337))
      | ~ v1_funct_1(C_338)
      | ~ l1_pre_topc(B_337)
      | ~ v2_pre_topc(B_337)
      | v2_struct_0(B_337)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1501,plain,(
    ! [D_339] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_339)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_339)
      | ~ m1_pre_topc(D_339,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_1499])).

tff(c_1504,plain,(
    ! [D_339] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_339)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_339)
      | ~ m1_pre_topc(D_339,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_1501])).

tff(c_1505,plain,(
    ! [D_339] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_339)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_339)
      | ~ m1_pre_topc(D_339,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_1504])).

tff(c_1589,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1543,c_1505])).

tff(c_1596,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1589])).

tff(c_1881,plain,(
    ! [A_405,C_408,D_407,E_406,B_409] :
      ( m1_subset_1(k3_tmap_1(A_405,B_409,k1_tsep_1(A_405,C_408,D_407),D_407,E_406),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_407),u1_struct_0(B_409))))
      | ~ v5_pre_topc(E_406,k1_tsep_1(A_405,C_408,D_407),B_409)
      | ~ m1_subset_1(E_406,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_405,C_408,D_407)),u1_struct_0(B_409))))
      | ~ v1_funct_2(E_406,u1_struct_0(k1_tsep_1(A_405,C_408,D_407)),u1_struct_0(B_409))
      | ~ v1_funct_1(E_406)
      | ~ r4_tsep_1(A_405,C_408,D_407)
      | ~ m1_pre_topc(D_407,A_405)
      | v2_struct_0(D_407)
      | ~ m1_pre_topc(C_408,A_405)
      | v2_struct_0(C_408)
      | ~ l1_pre_topc(B_409)
      | ~ v2_pre_topc(B_409)
      | v2_struct_0(B_409)
      | ~ l1_pre_topc(A_405)
      | ~ v2_pre_topc(A_405)
      | v2_struct_0(A_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1926,plain,(
    ! [B_409,E_406] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_409,'#skF_1','#skF_5',E_406),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_409))))
      | ~ v5_pre_topc(E_406,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_409)
      | ~ m1_subset_1(E_406,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_409))))
      | ~ v1_funct_2(E_406,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_409))
      | ~ v1_funct_1(E_406)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_409)
      | ~ v2_pre_topc(B_409)
      | v2_struct_0(B_409)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1881])).

tff(c_1954,plain,(
    ! [B_409,E_406] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_409,'#skF_1','#skF_5',E_406),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_409))))
      | ~ v5_pre_topc(E_406,'#skF_1',B_409)
      | ~ m1_subset_1(E_406,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_409))))
      | ~ v1_funct_2(E_406,u1_struct_0('#skF_1'),u1_struct_0(B_409))
      | ~ v1_funct_1(E_406)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_409)
      | ~ v2_pre_topc(B_409)
      | v2_struct_0(B_409)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_40,c_36,c_38,c_38,c_38,c_1926])).

tff(c_1999,plain,(
    ! [B_414,E_415] :
      ( m1_subset_1(k3_tmap_1('#skF_1',B_414,'#skF_1','#skF_5',E_415),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_414))))
      | ~ v5_pre_topc(E_415,'#skF_1',B_414)
      | ~ m1_subset_1(E_415,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_414))))
      | ~ v1_funct_2(E_415,u1_struct_0('#skF_1'),u1_struct_0(B_414))
      | ~ v1_funct_1(E_415)
      | ~ l1_pre_topc(B_414)
      | ~ v2_pre_topc(B_414)
      | v2_struct_0(B_414) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_1954])).

tff(c_2006,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1596,c_1999])).

tff(c_2012,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_1475,c_2006])).

tff(c_2014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1476,c_2012])).

tff(c_2016,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_2015,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_2035,plain,(
    ! [A_422,B_423,C_424] :
      ( m1_pre_topc(k1_tsep_1(A_422,B_423,C_424),A_422)
      | ~ m1_pre_topc(C_424,A_422)
      | v2_struct_0(C_424)
      | ~ m1_pre_topc(B_423,A_422)
      | v2_struct_0(B_423)
      | ~ l1_pre_topc(A_422)
      | v2_struct_0(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2038,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2035])).

tff(c_2040,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44,c_40,c_2038])).

tff(c_2041,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_2040])).

tff(c_2058,plain,(
    ! [D_432,E_431,A_434,C_433,B_430] :
      ( k3_tmap_1(A_434,B_430,C_433,D_432,E_431) = k2_partfun1(u1_struct_0(C_433),u1_struct_0(B_430),E_431,u1_struct_0(D_432))
      | ~ m1_pre_topc(D_432,C_433)
      | ~ m1_subset_1(E_431,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_433),u1_struct_0(B_430))))
      | ~ v1_funct_2(E_431,u1_struct_0(C_433),u1_struct_0(B_430))
      | ~ v1_funct_1(E_431)
      | ~ m1_pre_topc(D_432,A_434)
      | ~ m1_pre_topc(C_433,A_434)
      | ~ l1_pre_topc(B_430)
      | ~ v2_pre_topc(B_430)
      | v2_struct_0(B_430)
      | ~ l1_pre_topc(A_434)
      | ~ v2_pre_topc(A_434)
      | v2_struct_0(A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2060,plain,(
    ! [A_434,D_432] :
      ( k3_tmap_1(A_434,'#skF_2','#skF_1',D_432,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_432))
      | ~ m1_pre_topc(D_432,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_432,A_434)
      | ~ m1_pre_topc('#skF_1',A_434)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_434)
      | ~ v2_pre_topc(A_434)
      | v2_struct_0(A_434) ) ),
    inference(resolution,[status(thm)],[c_48,c_2058])).

tff(c_2063,plain,(
    ! [A_434,D_432] :
      ( k3_tmap_1(A_434,'#skF_2','#skF_1',D_432,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_432))
      | ~ m1_pre_topc(D_432,'#skF_1')
      | ~ m1_pre_topc(D_432,A_434)
      | ~ m1_pre_topc('#skF_1',A_434)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_434)
      | ~ v2_pre_topc(A_434)
      | v2_struct_0(A_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2060])).

tff(c_2071,plain,(
    ! [A_440,D_441] :
      ( k3_tmap_1(A_440,'#skF_2','#skF_1',D_441,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_441))
      | ~ m1_pre_topc(D_441,'#skF_1')
      | ~ m1_pre_topc(D_441,A_440)
      | ~ m1_pre_topc('#skF_1',A_440)
      | ~ l1_pre_topc(A_440)
      | ~ v2_pre_topc(A_440)
      | v2_struct_0(A_440) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2063])).

tff(c_2079,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2071])).

tff(c_2091,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2041,c_40,c_2079])).

tff(c_2092,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2091])).

tff(c_2042,plain,(
    ! [A_425,B_426,C_427,D_428] :
      ( k2_partfun1(u1_struct_0(A_425),u1_struct_0(B_426),C_427,u1_struct_0(D_428)) = k2_tmap_1(A_425,B_426,C_427,D_428)
      | ~ m1_pre_topc(D_428,A_425)
      | ~ m1_subset_1(C_427,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_425),u1_struct_0(B_426))))
      | ~ v1_funct_2(C_427,u1_struct_0(A_425),u1_struct_0(B_426))
      | ~ v1_funct_1(C_427)
      | ~ l1_pre_topc(B_426)
      | ~ v2_pre_topc(B_426)
      | v2_struct_0(B_426)
      | ~ l1_pre_topc(A_425)
      | ~ v2_pre_topc(A_425)
      | v2_struct_0(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2044,plain,(
    ! [D_428] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_428)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_428)
      | ~ m1_pre_topc(D_428,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_2042])).

tff(c_2047,plain,(
    ! [D_428] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_428)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_428)
      | ~ m1_pre_topc(D_428,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_2044])).

tff(c_2048,plain,(
    ! [D_428] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_428)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_428)
      | ~ m1_pre_topc(D_428,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_2047])).

tff(c_2174,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2092,c_2048])).

tff(c_2181,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2174])).

tff(c_2321,plain,(
    ! [E_476,B_479,A_475,C_478,D_477] :
      ( v1_funct_2(k3_tmap_1(A_475,B_479,k1_tsep_1(A_475,C_478,D_477),D_477,E_476),u1_struct_0(D_477),u1_struct_0(B_479))
      | ~ v5_pre_topc(E_476,k1_tsep_1(A_475,C_478,D_477),B_479)
      | ~ m1_subset_1(E_476,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_475,C_478,D_477)),u1_struct_0(B_479))))
      | ~ v1_funct_2(E_476,u1_struct_0(k1_tsep_1(A_475,C_478,D_477)),u1_struct_0(B_479))
      | ~ v1_funct_1(E_476)
      | ~ r4_tsep_1(A_475,C_478,D_477)
      | ~ m1_pre_topc(D_477,A_475)
      | v2_struct_0(D_477)
      | ~ m1_pre_topc(C_478,A_475)
      | v2_struct_0(C_478)
      | ~ l1_pre_topc(B_479)
      | ~ v2_pre_topc(B_479)
      | v2_struct_0(B_479)
      | ~ l1_pre_topc(A_475)
      | ~ v2_pre_topc(A_475)
      | v2_struct_0(A_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2323,plain,(
    ! [B_479,E_476] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_479,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_476),u1_struct_0('#skF_5'),u1_struct_0(B_479))
      | ~ v5_pre_topc(E_476,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_479)
      | ~ m1_subset_1(E_476,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_479))))
      | ~ v1_funct_2(E_476,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_479))
      | ~ v1_funct_1(E_476)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_479)
      | ~ v2_pre_topc(B_479)
      | v2_struct_0(B_479)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2321])).

tff(c_2325,plain,(
    ! [B_479,E_476] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_479,'#skF_1','#skF_5',E_476),u1_struct_0('#skF_5'),u1_struct_0(B_479))
      | ~ v5_pre_topc(E_476,'#skF_1',B_479)
      | ~ m1_subset_1(E_476,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_479))))
      | ~ v1_funct_2(E_476,u1_struct_0('#skF_1'),u1_struct_0(B_479))
      | ~ v1_funct_1(E_476)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_479)
      | ~ v2_pre_topc(B_479)
      | v2_struct_0(B_479)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_40,c_36,c_38,c_38,c_38,c_2323])).

tff(c_2327,plain,(
    ! [B_480,E_481] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_480,'#skF_1','#skF_5',E_481),u1_struct_0('#skF_5'),u1_struct_0(B_480))
      | ~ v5_pre_topc(E_481,'#skF_1',B_480)
      | ~ m1_subset_1(E_481,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_480))))
      | ~ v1_funct_2(E_481,u1_struct_0('#skF_1'),u1_struct_0(B_480))
      | ~ v1_funct_1(E_481)
      | ~ l1_pre_topc(B_480)
      | ~ v2_pre_topc(B_480)
      | v2_struct_0(B_480) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_2325])).

tff(c_2329,plain,
    ( v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2327])).

tff(c_2332,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2015,c_2181,c_2329])).

tff(c_2334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2016,c_2332])).

tff(c_2336,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_2335,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_2356,plain,(
    ! [A_488,B_489,C_490] :
      ( m1_pre_topc(k1_tsep_1(A_488,B_489,C_490),A_488)
      | ~ m1_pre_topc(C_490,A_488)
      | v2_struct_0(C_490)
      | ~ m1_pre_topc(B_489,A_488)
      | v2_struct_0(B_489)
      | ~ l1_pre_topc(A_488)
      | v2_struct_0(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2359,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2356])).

tff(c_2361,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44,c_40,c_2359])).

tff(c_2362,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_2361])).

tff(c_2370,plain,(
    ! [D_497,C_498,A_499,E_496,B_495] :
      ( k3_tmap_1(A_499,B_495,C_498,D_497,E_496) = k2_partfun1(u1_struct_0(C_498),u1_struct_0(B_495),E_496,u1_struct_0(D_497))
      | ~ m1_pre_topc(D_497,C_498)
      | ~ m1_subset_1(E_496,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_498),u1_struct_0(B_495))))
      | ~ v1_funct_2(E_496,u1_struct_0(C_498),u1_struct_0(B_495))
      | ~ v1_funct_1(E_496)
      | ~ m1_pre_topc(D_497,A_499)
      | ~ m1_pre_topc(C_498,A_499)
      | ~ l1_pre_topc(B_495)
      | ~ v2_pre_topc(B_495)
      | v2_struct_0(B_495)
      | ~ l1_pre_topc(A_499)
      | ~ v2_pre_topc(A_499)
      | v2_struct_0(A_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2372,plain,(
    ! [A_499,D_497] :
      ( k3_tmap_1(A_499,'#skF_2','#skF_1',D_497,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_497))
      | ~ m1_pre_topc(D_497,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_497,A_499)
      | ~ m1_pre_topc('#skF_1',A_499)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_499)
      | ~ v2_pre_topc(A_499)
      | v2_struct_0(A_499) ) ),
    inference(resolution,[status(thm)],[c_48,c_2370])).

tff(c_2375,plain,(
    ! [A_499,D_497] :
      ( k3_tmap_1(A_499,'#skF_2','#skF_1',D_497,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_497))
      | ~ m1_pre_topc(D_497,'#skF_1')
      | ~ m1_pre_topc(D_497,A_499)
      | ~ m1_pre_topc('#skF_1',A_499)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_499)
      | ~ v2_pre_topc(A_499)
      | v2_struct_0(A_499) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2372])).

tff(c_2386,plain,(
    ! [A_501,D_502] :
      ( k3_tmap_1(A_501,'#skF_2','#skF_1',D_502,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_502))
      | ~ m1_pre_topc(D_502,'#skF_1')
      | ~ m1_pre_topc(D_502,A_501)
      | ~ m1_pre_topc('#skF_1',A_501)
      | ~ l1_pre_topc(A_501)
      | ~ v2_pre_topc(A_501)
      | v2_struct_0(A_501) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2375])).

tff(c_2392,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2386])).

tff(c_2402,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2362,c_44,c_2392])).

tff(c_2403,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2402])).

tff(c_2363,plain,(
    ! [A_491,B_492,C_493,D_494] :
      ( k2_partfun1(u1_struct_0(A_491),u1_struct_0(B_492),C_493,u1_struct_0(D_494)) = k2_tmap_1(A_491,B_492,C_493,D_494)
      | ~ m1_pre_topc(D_494,A_491)
      | ~ m1_subset_1(C_493,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_491),u1_struct_0(B_492))))
      | ~ v1_funct_2(C_493,u1_struct_0(A_491),u1_struct_0(B_492))
      | ~ v1_funct_1(C_493)
      | ~ l1_pre_topc(B_492)
      | ~ v2_pre_topc(B_492)
      | v2_struct_0(B_492)
      | ~ l1_pre_topc(A_491)
      | ~ v2_pre_topc(A_491)
      | v2_struct_0(A_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2365,plain,(
    ! [D_494] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_494)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_494)
      | ~ m1_pre_topc(D_494,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_2363])).

tff(c_2368,plain,(
    ! [D_494] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_494)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_494)
      | ~ m1_pre_topc(D_494,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_2365])).

tff(c_2369,plain,(
    ! [D_494] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_494)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_494)
      | ~ m1_pre_topc(D_494,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_2368])).

tff(c_2489,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2403,c_2369])).

tff(c_2496,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2489])).

tff(c_2642,plain,(
    ! [E_542,C_544,D_543,A_541,B_545] :
      ( v1_funct_2(k3_tmap_1(A_541,B_545,k1_tsep_1(A_541,C_544,D_543),C_544,E_542),u1_struct_0(C_544),u1_struct_0(B_545))
      | ~ v5_pre_topc(E_542,k1_tsep_1(A_541,C_544,D_543),B_545)
      | ~ m1_subset_1(E_542,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_541,C_544,D_543)),u1_struct_0(B_545))))
      | ~ v1_funct_2(E_542,u1_struct_0(k1_tsep_1(A_541,C_544,D_543)),u1_struct_0(B_545))
      | ~ v1_funct_1(E_542)
      | ~ r4_tsep_1(A_541,C_544,D_543)
      | ~ m1_pre_topc(D_543,A_541)
      | v2_struct_0(D_543)
      | ~ m1_pre_topc(C_544,A_541)
      | v2_struct_0(C_544)
      | ~ l1_pre_topc(B_545)
      | ~ v2_pre_topc(B_545)
      | v2_struct_0(B_545)
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541)
      | v2_struct_0(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2644,plain,(
    ! [B_545,E_542] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_545,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_542),u1_struct_0('#skF_4'),u1_struct_0(B_545))
      | ~ v5_pre_topc(E_542,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_545)
      | ~ m1_subset_1(E_542,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_545))))
      | ~ v1_funct_2(E_542,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_545))
      | ~ v1_funct_1(E_542)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_545)
      | ~ v2_pre_topc(B_545)
      | v2_struct_0(B_545)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2642])).

tff(c_2646,plain,(
    ! [B_545,E_542] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_545,'#skF_1','#skF_4',E_542),u1_struct_0('#skF_4'),u1_struct_0(B_545))
      | ~ v5_pre_topc(E_542,'#skF_1',B_545)
      | ~ m1_subset_1(E_542,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_545))))
      | ~ v1_funct_2(E_542,u1_struct_0('#skF_1'),u1_struct_0(B_545))
      | ~ v1_funct_1(E_542)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_545)
      | ~ v2_pre_topc(B_545)
      | v2_struct_0(B_545)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_40,c_36,c_38,c_38,c_38,c_2644])).

tff(c_2648,plain,(
    ! [B_546,E_547] :
      ( v1_funct_2(k3_tmap_1('#skF_1',B_546,'#skF_1','#skF_4',E_547),u1_struct_0('#skF_4'),u1_struct_0(B_546))
      | ~ v5_pre_topc(E_547,'#skF_1',B_546)
      | ~ m1_subset_1(E_547,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_546))))
      | ~ v1_funct_2(E_547,u1_struct_0('#skF_1'),u1_struct_0(B_546))
      | ~ v1_funct_1(E_547)
      | ~ l1_pre_topc(B_546)
      | ~ v2_pre_topc(B_546)
      | v2_struct_0(B_546) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_2646])).

tff(c_2650,plain,
    ( v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2648])).

tff(c_2653,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2335,c_2496,c_2650])).

tff(c_2655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2336,c_2653])).

tff(c_2657,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_2656,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_2676,plain,(
    ! [A_554,B_555,C_556] :
      ( m1_pre_topc(k1_tsep_1(A_554,B_555,C_556),A_554)
      | ~ m1_pre_topc(C_556,A_554)
      | v2_struct_0(C_556)
      | ~ m1_pre_topc(B_555,A_554)
      | v2_struct_0(B_555)
      | ~ l1_pre_topc(A_554)
      | v2_struct_0(A_554) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2679,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2676])).

tff(c_2681,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44,c_40,c_2679])).

tff(c_2682,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_2681])).

tff(c_2699,plain,(
    ! [D_564,A_566,C_565,B_562,E_563] :
      ( k3_tmap_1(A_566,B_562,C_565,D_564,E_563) = k2_partfun1(u1_struct_0(C_565),u1_struct_0(B_562),E_563,u1_struct_0(D_564))
      | ~ m1_pre_topc(D_564,C_565)
      | ~ m1_subset_1(E_563,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_565),u1_struct_0(B_562))))
      | ~ v1_funct_2(E_563,u1_struct_0(C_565),u1_struct_0(B_562))
      | ~ v1_funct_1(E_563)
      | ~ m1_pre_topc(D_564,A_566)
      | ~ m1_pre_topc(C_565,A_566)
      | ~ l1_pre_topc(B_562)
      | ~ v2_pre_topc(B_562)
      | v2_struct_0(B_562)
      | ~ l1_pre_topc(A_566)
      | ~ v2_pre_topc(A_566)
      | v2_struct_0(A_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2701,plain,(
    ! [A_566,D_564] :
      ( k3_tmap_1(A_566,'#skF_2','#skF_1',D_564,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_564))
      | ~ m1_pre_topc(D_564,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_564,A_566)
      | ~ m1_pre_topc('#skF_1',A_566)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_566)
      | ~ v2_pre_topc(A_566)
      | v2_struct_0(A_566) ) ),
    inference(resolution,[status(thm)],[c_48,c_2699])).

tff(c_2704,plain,(
    ! [A_566,D_564] :
      ( k3_tmap_1(A_566,'#skF_2','#skF_1',D_564,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_564))
      | ~ m1_pre_topc(D_564,'#skF_1')
      | ~ m1_pre_topc(D_564,A_566)
      | ~ m1_pre_topc('#skF_1',A_566)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_566)
      | ~ v2_pre_topc(A_566)
      | v2_struct_0(A_566) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2701])).

tff(c_2706,plain,(
    ! [A_567,D_568] :
      ( k3_tmap_1(A_567,'#skF_2','#skF_1',D_568,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_568))
      | ~ m1_pre_topc(D_568,'#skF_1')
      | ~ m1_pre_topc(D_568,A_567)
      | ~ m1_pre_topc('#skF_1',A_567)
      | ~ l1_pre_topc(A_567)
      | ~ v2_pre_topc(A_567)
      | v2_struct_0(A_567) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2704])).

tff(c_2712,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2706])).

tff(c_2722,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2682,c_44,c_2712])).

tff(c_2723,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2722])).

tff(c_2683,plain,(
    ! [A_557,B_558,C_559,D_560] :
      ( k2_partfun1(u1_struct_0(A_557),u1_struct_0(B_558),C_559,u1_struct_0(D_560)) = k2_tmap_1(A_557,B_558,C_559,D_560)
      | ~ m1_pre_topc(D_560,A_557)
      | ~ m1_subset_1(C_559,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_557),u1_struct_0(B_558))))
      | ~ v1_funct_2(C_559,u1_struct_0(A_557),u1_struct_0(B_558))
      | ~ v1_funct_1(C_559)
      | ~ l1_pre_topc(B_558)
      | ~ v2_pre_topc(B_558)
      | v2_struct_0(B_558)
      | ~ l1_pre_topc(A_557)
      | ~ v2_pre_topc(A_557)
      | v2_struct_0(A_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2685,plain,(
    ! [D_560] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_560)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_560)
      | ~ m1_pre_topc(D_560,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_2683])).

tff(c_2688,plain,(
    ! [D_560] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_560)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_560)
      | ~ m1_pre_topc(D_560,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_2685])).

tff(c_2689,plain,(
    ! [D_560] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_560)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_560)
      | ~ m1_pre_topc(D_560,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_2688])).

tff(c_2767,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2723,c_2689])).

tff(c_2774,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2767])).

tff(c_2949,plain,(
    ! [E_601,A_600,C_603,B_604,D_602] :
      ( v5_pre_topc(k3_tmap_1(A_600,B_604,k1_tsep_1(A_600,C_603,D_602),C_603,E_601),C_603,B_604)
      | ~ v5_pre_topc(E_601,k1_tsep_1(A_600,C_603,D_602),B_604)
      | ~ m1_subset_1(E_601,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_600,C_603,D_602)),u1_struct_0(B_604))))
      | ~ v1_funct_2(E_601,u1_struct_0(k1_tsep_1(A_600,C_603,D_602)),u1_struct_0(B_604))
      | ~ v1_funct_1(E_601)
      | ~ r4_tsep_1(A_600,C_603,D_602)
      | ~ m1_pre_topc(D_602,A_600)
      | v2_struct_0(D_602)
      | ~ m1_pre_topc(C_603,A_600)
      | v2_struct_0(C_603)
      | ~ l1_pre_topc(B_604)
      | ~ v2_pre_topc(B_604)
      | v2_struct_0(B_604)
      | ~ l1_pre_topc(A_600)
      | ~ v2_pre_topc(A_600)
      | v2_struct_0(A_600) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2951,plain,(
    ! [B_604,E_601] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_604,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_601),'#skF_4',B_604)
      | ~ v5_pre_topc(E_601,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_604)
      | ~ m1_subset_1(E_601,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_604))))
      | ~ v1_funct_2(E_601,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_604))
      | ~ v1_funct_1(E_601)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_604)
      | ~ v2_pre_topc(B_604)
      | v2_struct_0(B_604)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2949])).

tff(c_2953,plain,(
    ! [B_604,E_601] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_604,'#skF_1','#skF_4',E_601),'#skF_4',B_604)
      | ~ v5_pre_topc(E_601,'#skF_1',B_604)
      | ~ m1_subset_1(E_601,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_604))))
      | ~ v1_funct_2(E_601,u1_struct_0('#skF_1'),u1_struct_0(B_604))
      | ~ v1_funct_1(E_601)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_604)
      | ~ v2_pre_topc(B_604)
      | v2_struct_0(B_604)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_40,c_36,c_38,c_38,c_38,c_2951])).

tff(c_2955,plain,(
    ! [B_605,E_606] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_605,'#skF_1','#skF_4',E_606),'#skF_4',B_605)
      | ~ v5_pre_topc(E_606,'#skF_1',B_605)
      | ~ m1_subset_1(E_606,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_605))))
      | ~ v1_funct_2(E_606,u1_struct_0('#skF_1'),u1_struct_0(B_605))
      | ~ v1_funct_1(E_606)
      | ~ l1_pre_topc(B_605)
      | ~ v2_pre_topc(B_605)
      | v2_struct_0(B_605) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_2953])).

tff(c_2957,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2955])).

tff(c_2960,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2656,c_2774,c_2957])).

tff(c_2962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2657,c_2960])).

tff(c_2964,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2963,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2984,plain,(
    ! [A_613,B_614,C_615] :
      ( m1_pre_topc(k1_tsep_1(A_613,B_614,C_615),A_613)
      | ~ m1_pre_topc(C_615,A_613)
      | v2_struct_0(C_615)
      | ~ m1_pre_topc(B_614,A_613)
      | v2_struct_0(B_614)
      | ~ l1_pre_topc(A_613)
      | v2_struct_0(A_613) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2987,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2984])).

tff(c_2989,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44,c_40,c_2987])).

tff(c_2990,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_2989])).

tff(c_3009,plain,(
    ! [D_623,A_625,E_622,C_624,B_621] :
      ( k3_tmap_1(A_625,B_621,C_624,D_623,E_622) = k2_partfun1(u1_struct_0(C_624),u1_struct_0(B_621),E_622,u1_struct_0(D_623))
      | ~ m1_pre_topc(D_623,C_624)
      | ~ m1_subset_1(E_622,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_624),u1_struct_0(B_621))))
      | ~ v1_funct_2(E_622,u1_struct_0(C_624),u1_struct_0(B_621))
      | ~ v1_funct_1(E_622)
      | ~ m1_pre_topc(D_623,A_625)
      | ~ m1_pre_topc(C_624,A_625)
      | ~ l1_pre_topc(B_621)
      | ~ v2_pre_topc(B_621)
      | v2_struct_0(B_621)
      | ~ l1_pre_topc(A_625)
      | ~ v2_pre_topc(A_625)
      | v2_struct_0(A_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3011,plain,(
    ! [A_625,D_623] :
      ( k3_tmap_1(A_625,'#skF_2','#skF_1',D_623,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_623))
      | ~ m1_pre_topc(D_623,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_623,A_625)
      | ~ m1_pre_topc('#skF_1',A_625)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_625)
      | ~ v2_pre_topc(A_625)
      | v2_struct_0(A_625) ) ),
    inference(resolution,[status(thm)],[c_48,c_3009])).

tff(c_3014,plain,(
    ! [A_625,D_623] :
      ( k3_tmap_1(A_625,'#skF_2','#skF_1',D_623,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_623))
      | ~ m1_pre_topc(D_623,'#skF_1')
      | ~ m1_pre_topc(D_623,A_625)
      | ~ m1_pre_topc('#skF_1',A_625)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_625)
      | ~ v2_pre_topc(A_625)
      | v2_struct_0(A_625) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_3011])).

tff(c_3016,plain,(
    ! [A_626,D_627] :
      ( k3_tmap_1(A_626,'#skF_2','#skF_1',D_627,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_627))
      | ~ m1_pre_topc(D_627,'#skF_1')
      | ~ m1_pre_topc(D_627,A_626)
      | ~ m1_pre_topc('#skF_1',A_626)
      | ~ l1_pre_topc(A_626)
      | ~ v2_pre_topc(A_626)
      | v2_struct_0(A_626) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3014])).

tff(c_3024,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_3016])).

tff(c_3036,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2990,c_40,c_3024])).

tff(c_3037,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3036])).

tff(c_2991,plain,(
    ! [A_616,B_617,C_618,D_619] :
      ( k2_partfun1(u1_struct_0(A_616),u1_struct_0(B_617),C_618,u1_struct_0(D_619)) = k2_tmap_1(A_616,B_617,C_618,D_619)
      | ~ m1_pre_topc(D_619,A_616)
      | ~ m1_subset_1(C_618,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_616),u1_struct_0(B_617))))
      | ~ v1_funct_2(C_618,u1_struct_0(A_616),u1_struct_0(B_617))
      | ~ v1_funct_1(C_618)
      | ~ l1_pre_topc(B_617)
      | ~ v2_pre_topc(B_617)
      | v2_struct_0(B_617)
      | ~ l1_pre_topc(A_616)
      | ~ v2_pre_topc(A_616)
      | v2_struct_0(A_616) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2993,plain,(
    ! [D_619] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_619)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_619)
      | ~ m1_pre_topc(D_619,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_2991])).

tff(c_2996,plain,(
    ! [D_619] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_619)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_619)
      | ~ m1_pre_topc(D_619,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_2993])).

tff(c_2997,plain,(
    ! [D_619] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_619)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_619)
      | ~ m1_pre_topc(D_619,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_2996])).

tff(c_3083,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3037,c_2997])).

tff(c_3090,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3083])).

tff(c_3246,plain,(
    ! [C_655,B_656,A_652,D_654,E_653] :
      ( v5_pre_topc(k3_tmap_1(A_652,B_656,k1_tsep_1(A_652,C_655,D_654),D_654,E_653),D_654,B_656)
      | ~ v5_pre_topc(E_653,k1_tsep_1(A_652,C_655,D_654),B_656)
      | ~ m1_subset_1(E_653,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_652,C_655,D_654)),u1_struct_0(B_656))))
      | ~ v1_funct_2(E_653,u1_struct_0(k1_tsep_1(A_652,C_655,D_654)),u1_struct_0(B_656))
      | ~ v1_funct_1(E_653)
      | ~ r4_tsep_1(A_652,C_655,D_654)
      | ~ m1_pre_topc(D_654,A_652)
      | v2_struct_0(D_654)
      | ~ m1_pre_topc(C_655,A_652)
      | v2_struct_0(C_655)
      | ~ l1_pre_topc(B_656)
      | ~ v2_pre_topc(B_656)
      | v2_struct_0(B_656)
      | ~ l1_pre_topc(A_652)
      | ~ v2_pre_topc(A_652)
      | v2_struct_0(A_652) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_3248,plain,(
    ! [B_656,E_653] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_656,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_653),'#skF_5',B_656)
      | ~ v5_pre_topc(E_653,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_656)
      | ~ m1_subset_1(E_653,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_656))))
      | ~ v1_funct_2(E_653,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_656))
      | ~ v1_funct_1(E_653)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_656)
      | ~ v2_pre_topc(B_656)
      | v2_struct_0(B_656)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3246])).

tff(c_3250,plain,(
    ! [B_656,E_653] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_656,'#skF_1','#skF_5',E_653),'#skF_5',B_656)
      | ~ v5_pre_topc(E_653,'#skF_1',B_656)
      | ~ m1_subset_1(E_653,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_656))))
      | ~ v1_funct_2(E_653,u1_struct_0('#skF_1'),u1_struct_0(B_656))
      | ~ v1_funct_1(E_653)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_656)
      | ~ v2_pre_topc(B_656)
      | v2_struct_0(B_656)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_40,c_36,c_38,c_38,c_38,c_3248])).

tff(c_3252,plain,(
    ! [B_657,E_658] :
      ( v5_pre_topc(k3_tmap_1('#skF_1',B_657,'#skF_1','#skF_5',E_658),'#skF_5',B_657)
      | ~ v5_pre_topc(E_658,'#skF_1',B_657)
      | ~ m1_subset_1(E_658,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_657))))
      | ~ v1_funct_2(E_658,u1_struct_0('#skF_1'),u1_struct_0(B_657))
      | ~ v1_funct_1(E_658)
      | ~ l1_pre_topc(B_657)
      | ~ v2_pre_topc(B_657)
      | v2_struct_0(B_657) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_3250])).

tff(c_3254,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'),'#skF_5','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_3252])).

tff(c_3257,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2963,c_3090,c_3254])).

tff(c_3259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2964,c_3257])).

tff(c_3261,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_3260,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_3282,plain,(
    ! [A_665,B_666,C_667] :
      ( m1_pre_topc(k1_tsep_1(A_665,B_666,C_667),A_665)
      | ~ m1_pre_topc(C_667,A_665)
      | v2_struct_0(C_667)
      | ~ m1_pre_topc(B_666,A_665)
      | v2_struct_0(B_666)
      | ~ l1_pre_topc(A_665)
      | v2_struct_0(A_665) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3285,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3282])).

tff(c_3287,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44,c_40,c_3285])).

tff(c_3288,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_3287])).

tff(c_3305,plain,(
    ! [D_675,B_673,E_674,A_677,C_676] :
      ( k3_tmap_1(A_677,B_673,C_676,D_675,E_674) = k2_partfun1(u1_struct_0(C_676),u1_struct_0(B_673),E_674,u1_struct_0(D_675))
      | ~ m1_pre_topc(D_675,C_676)
      | ~ m1_subset_1(E_674,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_676),u1_struct_0(B_673))))
      | ~ v1_funct_2(E_674,u1_struct_0(C_676),u1_struct_0(B_673))
      | ~ v1_funct_1(E_674)
      | ~ m1_pre_topc(D_675,A_677)
      | ~ m1_pre_topc(C_676,A_677)
      | ~ l1_pre_topc(B_673)
      | ~ v2_pre_topc(B_673)
      | v2_struct_0(B_673)
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3307,plain,(
    ! [A_677,D_675] :
      ( k3_tmap_1(A_677,'#skF_2','#skF_1',D_675,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_675))
      | ~ m1_pre_topc(D_675,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_675,A_677)
      | ~ m1_pre_topc('#skF_1',A_677)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677) ) ),
    inference(resolution,[status(thm)],[c_48,c_3305])).

tff(c_3310,plain,(
    ! [A_677,D_675] :
      ( k3_tmap_1(A_677,'#skF_2','#skF_1',D_675,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_675))
      | ~ m1_pre_topc(D_675,'#skF_1')
      | ~ m1_pre_topc(D_675,A_677)
      | ~ m1_pre_topc('#skF_1',A_677)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_3307])).

tff(c_3312,plain,(
    ! [A_678,D_679] :
      ( k3_tmap_1(A_678,'#skF_2','#skF_1',D_679,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_679))
      | ~ m1_pre_topc(D_679,'#skF_1')
      | ~ m1_pre_topc(D_679,A_678)
      | ~ m1_pre_topc('#skF_1',A_678)
      | ~ l1_pre_topc(A_678)
      | ~ v2_pre_topc(A_678)
      | v2_struct_0(A_678) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3310])).

tff(c_3318,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_3312])).

tff(c_3328,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_3288,c_44,c_3318])).

tff(c_3329,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3328])).

tff(c_3289,plain,(
    ! [A_668,B_669,C_670,D_671] :
      ( k2_partfun1(u1_struct_0(A_668),u1_struct_0(B_669),C_670,u1_struct_0(D_671)) = k2_tmap_1(A_668,B_669,C_670,D_671)
      | ~ m1_pre_topc(D_671,A_668)
      | ~ m1_subset_1(C_670,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_668),u1_struct_0(B_669))))
      | ~ v1_funct_2(C_670,u1_struct_0(A_668),u1_struct_0(B_669))
      | ~ v1_funct_1(C_670)
      | ~ l1_pre_topc(B_669)
      | ~ v2_pre_topc(B_669)
      | v2_struct_0(B_669)
      | ~ l1_pre_topc(A_668)
      | ~ v2_pre_topc(A_668)
      | v2_struct_0(A_668) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3291,plain,(
    ! [D_671] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_671)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_671)
      | ~ m1_pre_topc(D_671,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_3289])).

tff(c_3294,plain,(
    ! [D_671] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_671)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_671)
      | ~ m1_pre_topc(D_671,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_3291])).

tff(c_3295,plain,(
    ! [D_671] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_671)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_671)
      | ~ m1_pre_topc(D_671,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_3294])).

tff(c_3379,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3329,c_3295])).

tff(c_3386,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3379])).

tff(c_3448,plain,(
    ! [D_687,C_688,A_685,B_689,E_686] :
      ( v1_funct_1(k3_tmap_1(A_685,B_689,k1_tsep_1(A_685,C_688,D_687),C_688,E_686))
      | ~ v5_pre_topc(E_686,k1_tsep_1(A_685,C_688,D_687),B_689)
      | ~ m1_subset_1(E_686,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_685,C_688,D_687)),u1_struct_0(B_689))))
      | ~ v1_funct_2(E_686,u1_struct_0(k1_tsep_1(A_685,C_688,D_687)),u1_struct_0(B_689))
      | ~ v1_funct_1(E_686)
      | ~ r4_tsep_1(A_685,C_688,D_687)
      | ~ m1_pre_topc(D_687,A_685)
      | v2_struct_0(D_687)
      | ~ m1_pre_topc(C_688,A_685)
      | v2_struct_0(C_688)
      | ~ l1_pre_topc(B_689)
      | ~ v2_pre_topc(B_689)
      | v2_struct_0(B_689)
      | ~ l1_pre_topc(A_685)
      | ~ v2_pre_topc(A_685)
      | v2_struct_0(A_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_3450,plain,(
    ! [B_689,E_686] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_689,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_686))
      | ~ v5_pre_topc(E_686,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_689)
      | ~ m1_subset_1(E_686,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_689))))
      | ~ v1_funct_2(E_686,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_689))
      | ~ v1_funct_1(E_686)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_689)
      | ~ v2_pre_topc(B_689)
      | v2_struct_0(B_689)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3448])).

tff(c_3452,plain,(
    ! [B_689,E_686] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_689,'#skF_1','#skF_4',E_686))
      | ~ v5_pre_topc(E_686,'#skF_1',B_689)
      | ~ m1_subset_1(E_686,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_689))))
      | ~ v1_funct_2(E_686,u1_struct_0('#skF_1'),u1_struct_0(B_689))
      | ~ v1_funct_1(E_686)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_689)
      | ~ v2_pre_topc(B_689)
      | v2_struct_0(B_689)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_40,c_36,c_38,c_38,c_38,c_3450])).

tff(c_3462,plain,(
    ! [B_692,E_693] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_692,'#skF_1','#skF_4',E_693))
      | ~ v5_pre_topc(E_693,'#skF_1',B_692)
      | ~ m1_subset_1(E_693,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_692))))
      | ~ v1_funct_2(E_693,u1_struct_0('#skF_1'),u1_struct_0(B_692))
      | ~ v1_funct_1(E_693)
      | ~ l1_pre_topc(B_692)
      | ~ v2_pre_topc(B_692)
      | v2_struct_0(B_692) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_3452])).

tff(c_3465,plain,
    ( v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_3462])).

tff(c_3468,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_3260,c_3386,c_3465])).

tff(c_3470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3261,c_3468])).

tff(c_3472,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_3471,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_3494,plain,(
    ! [A_700,B_701,C_702] :
      ( m1_pre_topc(k1_tsep_1(A_700,B_701,C_702),A_700)
      | ~ m1_pre_topc(C_702,A_700)
      | v2_struct_0(C_702)
      | ~ m1_pre_topc(B_701,A_700)
      | v2_struct_0(B_701)
      | ~ l1_pre_topc(A_700)
      | v2_struct_0(A_700) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3497,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3494])).

tff(c_3499,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44,c_40,c_3497])).

tff(c_3500,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_3499])).

tff(c_3517,plain,(
    ! [A_712,D_710,C_711,E_709,B_708] :
      ( k3_tmap_1(A_712,B_708,C_711,D_710,E_709) = k2_partfun1(u1_struct_0(C_711),u1_struct_0(B_708),E_709,u1_struct_0(D_710))
      | ~ m1_pre_topc(D_710,C_711)
      | ~ m1_subset_1(E_709,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_711),u1_struct_0(B_708))))
      | ~ v1_funct_2(E_709,u1_struct_0(C_711),u1_struct_0(B_708))
      | ~ v1_funct_1(E_709)
      | ~ m1_pre_topc(D_710,A_712)
      | ~ m1_pre_topc(C_711,A_712)
      | ~ l1_pre_topc(B_708)
      | ~ v2_pre_topc(B_708)
      | v2_struct_0(B_708)
      | ~ l1_pre_topc(A_712)
      | ~ v2_pre_topc(A_712)
      | v2_struct_0(A_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3519,plain,(
    ! [A_712,D_710] :
      ( k3_tmap_1(A_712,'#skF_2','#skF_1',D_710,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_710))
      | ~ m1_pre_topc(D_710,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_710,A_712)
      | ~ m1_pre_topc('#skF_1',A_712)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_712)
      | ~ v2_pre_topc(A_712)
      | v2_struct_0(A_712) ) ),
    inference(resolution,[status(thm)],[c_48,c_3517])).

tff(c_3522,plain,(
    ! [A_712,D_710] :
      ( k3_tmap_1(A_712,'#skF_2','#skF_1',D_710,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_710))
      | ~ m1_pre_topc(D_710,'#skF_1')
      | ~ m1_pre_topc(D_710,A_712)
      | ~ m1_pre_topc('#skF_1',A_712)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_712)
      | ~ v2_pre_topc(A_712)
      | v2_struct_0(A_712) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_3519])).

tff(c_3530,plain,(
    ! [A_718,D_719] :
      ( k3_tmap_1(A_718,'#skF_2','#skF_1',D_719,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_719))
      | ~ m1_pre_topc(D_719,'#skF_1')
      | ~ m1_pre_topc(D_719,A_718)
      | ~ m1_pre_topc('#skF_1',A_718)
      | ~ l1_pre_topc(A_718)
      | ~ v2_pre_topc(A_718)
      | v2_struct_0(A_718) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3522])).

tff(c_3538,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_3530])).

tff(c_3550,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_3500,c_40,c_3538])).

tff(c_3551,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3550])).

tff(c_3501,plain,(
    ! [A_703,B_704,C_705,D_706] :
      ( k2_partfun1(u1_struct_0(A_703),u1_struct_0(B_704),C_705,u1_struct_0(D_706)) = k2_tmap_1(A_703,B_704,C_705,D_706)
      | ~ m1_pre_topc(D_706,A_703)
      | ~ m1_subset_1(C_705,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_703),u1_struct_0(B_704))))
      | ~ v1_funct_2(C_705,u1_struct_0(A_703),u1_struct_0(B_704))
      | ~ v1_funct_1(C_705)
      | ~ l1_pre_topc(B_704)
      | ~ v2_pre_topc(B_704)
      | v2_struct_0(B_704)
      | ~ l1_pre_topc(A_703)
      | ~ v2_pre_topc(A_703)
      | v2_struct_0(A_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3503,plain,(
    ! [D_706] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_706)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_706)
      | ~ m1_pre_topc(D_706,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_3501])).

tff(c_3506,plain,(
    ! [D_706] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_706)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_706)
      | ~ m1_pre_topc(D_706,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_3503])).

tff(c_3507,plain,(
    ! [D_706] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_706)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_706)
      | ~ m1_pre_topc(D_706,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_3506])).

tff(c_3633,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3551,c_3507])).

tff(c_3640,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3633])).

tff(c_3624,plain,(
    ! [B_724,C_723,D_722,E_721,A_720] :
      ( v1_funct_1(k3_tmap_1(A_720,B_724,k1_tsep_1(A_720,C_723,D_722),D_722,E_721))
      | ~ v5_pre_topc(E_721,k1_tsep_1(A_720,C_723,D_722),B_724)
      | ~ m1_subset_1(E_721,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_720,C_723,D_722)),u1_struct_0(B_724))))
      | ~ v1_funct_2(E_721,u1_struct_0(k1_tsep_1(A_720,C_723,D_722)),u1_struct_0(B_724))
      | ~ v1_funct_1(E_721)
      | ~ r4_tsep_1(A_720,C_723,D_722)
      | ~ m1_pre_topc(D_722,A_720)
      | v2_struct_0(D_722)
      | ~ m1_pre_topc(C_723,A_720)
      | v2_struct_0(C_723)
      | ~ l1_pre_topc(B_724)
      | ~ v2_pre_topc(B_724)
      | v2_struct_0(B_724)
      | ~ l1_pre_topc(A_720)
      | ~ v2_pre_topc(A_720)
      | v2_struct_0(A_720) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_3626,plain,(
    ! [B_724,E_721] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_724,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_721))
      | ~ v5_pre_topc(E_721,k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_724)
      | ~ m1_subset_1(E_721,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_724))))
      | ~ v1_funct_2(E_721,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_724))
      | ~ v1_funct_1(E_721)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_724)
      | ~ v2_pre_topc(B_724)
      | v2_struct_0(B_724)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3624])).

tff(c_3628,plain,(
    ! [B_724,E_721] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_724,'#skF_1','#skF_5',E_721))
      | ~ v5_pre_topc(E_721,'#skF_1',B_724)
      | ~ m1_subset_1(E_721,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_724))))
      | ~ v1_funct_2(E_721,u1_struct_0('#skF_1'),u1_struct_0(B_724))
      | ~ v1_funct_1(E_721)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_724)
      | ~ v2_pre_topc(B_724)
      | v2_struct_0(B_724)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_40,c_36,c_38,c_38,c_38,c_3626])).

tff(c_3674,plain,(
    ! [B_727,E_728] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_727,'#skF_1','#skF_5',E_728))
      | ~ v5_pre_topc(E_728,'#skF_1',B_727)
      | ~ m1_subset_1(E_728,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_727))))
      | ~ v1_funct_2(E_728,u1_struct_0('#skF_1'),u1_struct_0(B_727))
      | ~ v1_funct_1(E_728)
      | ~ l1_pre_topc(B_727)
      | ~ v2_pre_topc(B_727)
      | v2_struct_0(B_727) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_3628])).

tff(c_3677,plain,
    ( v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_3674])).

tff(c_3680,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_3471,c_3640,c_3677])).

tff(c_3682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3472,c_3680])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:51:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.34/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.53/2.45  
% 7.53/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.53/2.45  %$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.53/2.45  
% 7.53/2.45  %Foreground sorts:
% 7.53/2.45  
% 7.53/2.45  
% 7.53/2.45  %Background operators:
% 7.53/2.45  
% 7.53/2.45  
% 7.53/2.45  %Foreground operators:
% 7.53/2.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.53/2.45  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 7.53/2.45  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.53/2.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.53/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.53/2.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.53/2.45  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 7.53/2.45  tff('#skF_5', type, '#skF_5': $i).
% 7.53/2.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.53/2.45  tff('#skF_2', type, '#skF_2': $i).
% 7.53/2.45  tff('#skF_3', type, '#skF_3': $i).
% 7.53/2.45  tff('#skF_1', type, '#skF_1': $i).
% 7.53/2.45  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.53/2.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.53/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.53/2.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.53/2.45  tff('#skF_4', type, '#skF_4': $i).
% 7.53/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.53/2.45  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.53/2.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.53/2.45  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.53/2.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.53/2.45  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.53/2.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.53/2.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.53/2.45  
% 7.53/2.50  tff(f_229, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (((A = k1_tsep_1(A, D, E)) & r4_tsep_1(A, D, E)) => ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, C, E))) & v1_funct_2(k2_tmap_1(A, B, C, E), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, E), E, B)) & m1_subset_1(k2_tmap_1(A, B, C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_tmap_1)).
% 7.53/2.50  tff(f_106, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 7.53/2.50  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 7.53/2.50  tff(f_52, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.53/2.50  tff(f_166, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_tmap_1)).
% 7.53/2.50  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_150, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_190, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_150])).
% 7.53/2.50  tff(c_140, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_193, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_140])).
% 7.53/2.50  tff(c_130, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_192, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_130])).
% 7.53/2.50  tff(c_120, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_196, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_120])).
% 7.53/2.50  tff(c_110, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_189, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_110])).
% 7.53/2.50  tff(c_100, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_194, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_100])).
% 7.53/2.50  tff(c_90, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_191, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_90])).
% 7.53/2.50  tff(c_80, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_195, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_80])).
% 7.53/2.50  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_66, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_164, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_66])).
% 7.53/2.50  tff(c_174, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_164])).
% 7.53/2.50  tff(c_184, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_174])).
% 7.53/2.50  tff(c_654, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_193, c_192, c_196, c_189, c_194, c_191, c_195, c_184])).
% 7.53/2.50  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_40, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_38, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_211, plain, (![A_113, B_114, C_115]: (m1_pre_topc(k1_tsep_1(A_113, B_114, C_115), A_113) | ~m1_pre_topc(C_115, A_113) | v2_struct_0(C_115) | ~m1_pre_topc(B_114, A_113) | v2_struct_0(B_114) | ~l1_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.50  tff(c_214, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_211])).
% 7.53/2.50  tff(c_216, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44, c_40, c_214])).
% 7.53/2.50  tff(c_217, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_216])).
% 7.53/2.50  tff(c_248, plain, (![B_121, E_122, D_123, A_125, C_124]: (k3_tmap_1(A_125, B_121, C_124, D_123, E_122)=k2_partfun1(u1_struct_0(C_124), u1_struct_0(B_121), E_122, u1_struct_0(D_123)) | ~m1_pre_topc(D_123, C_124) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_124), u1_struct_0(B_121)))) | ~v1_funct_2(E_122, u1_struct_0(C_124), u1_struct_0(B_121)) | ~v1_funct_1(E_122) | ~m1_pre_topc(D_123, A_125) | ~m1_pre_topc(C_124, A_125) | ~l1_pre_topc(B_121) | ~v2_pre_topc(B_121) | v2_struct_0(B_121) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.53/2.50  tff(c_254, plain, (![A_125, D_123]: (k3_tmap_1(A_125, '#skF_2', '#skF_1', D_123, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_123)) | ~m1_pre_topc(D_123, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_123, A_125) | ~m1_pre_topc('#skF_1', A_125) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125))), inference(resolution, [status(thm)], [c_48, c_248])).
% 7.53/2.50  tff(c_265, plain, (![A_125, D_123]: (k3_tmap_1(A_125, '#skF_2', '#skF_1', D_123, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_123)) | ~m1_pre_topc(D_123, '#skF_1') | ~m1_pre_topc(D_123, A_125) | ~m1_pre_topc('#skF_1', A_125) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_254])).
% 7.53/2.50  tff(c_267, plain, (![A_126, D_127]: (k3_tmap_1(A_126, '#skF_2', '#skF_1', D_127, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_127)) | ~m1_pre_topc(D_127, '#skF_1') | ~m1_pre_topc(D_127, A_126) | ~m1_pre_topc('#skF_1', A_126) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(negUnitSimplification, [status(thm)], [c_58, c_265])).
% 7.53/2.50  tff(c_273, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_267])).
% 7.53/2.50  tff(c_283, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_217, c_44, c_273])).
% 7.53/2.50  tff(c_284, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_283])).
% 7.53/2.50  tff(c_218, plain, (![A_116, B_117, C_118, D_119]: (k2_partfun1(u1_struct_0(A_116), u1_struct_0(B_117), C_118, u1_struct_0(D_119))=k2_tmap_1(A_116, B_117, C_118, D_119) | ~m1_pre_topc(D_119, A_116) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116), u1_struct_0(B_117)))) | ~v1_funct_2(C_118, u1_struct_0(A_116), u1_struct_0(B_117)) | ~v1_funct_1(C_118) | ~l1_pre_topc(B_117) | ~v2_pre_topc(B_117) | v2_struct_0(B_117) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.53/2.50  tff(c_224, plain, (![D_119]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_119))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_119) | ~m1_pre_topc(D_119, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_218])).
% 7.53/2.50  tff(c_235, plain, (![D_119]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_119))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_119) | ~m1_pre_topc(D_119, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_224])).
% 7.53/2.50  tff(c_236, plain, (![D_119]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_119))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_119) | ~m1_pre_topc(D_119, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_235])).
% 7.53/2.50  tff(c_370, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_284, c_236])).
% 7.53/2.50  tff(c_377, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_370])).
% 7.53/2.50  tff(c_275, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_267])).
% 7.53/2.50  tff(c_287, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_217, c_40, c_275])).
% 7.53/2.50  tff(c_288, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_287])).
% 7.53/2.50  tff(c_334, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_288, c_236])).
% 7.53/2.50  tff(c_341, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_334])).
% 7.53/2.50  tff(c_36, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_229])).
% 7.53/2.50  tff(c_852, plain, (![B_212, C_211, D_210, E_209, A_208]: (v5_pre_topc(E_209, k1_tsep_1(A_208, C_211, D_210), B_212) | ~m1_subset_1(k3_tmap_1(A_208, B_212, k1_tsep_1(A_208, C_211, D_210), D_210, E_209), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_210), u1_struct_0(B_212)))) | ~v5_pre_topc(k3_tmap_1(A_208, B_212, k1_tsep_1(A_208, C_211, D_210), D_210, E_209), D_210, B_212) | ~v1_funct_2(k3_tmap_1(A_208, B_212, k1_tsep_1(A_208, C_211, D_210), D_210, E_209), u1_struct_0(D_210), u1_struct_0(B_212)) | ~v1_funct_1(k3_tmap_1(A_208, B_212, k1_tsep_1(A_208, C_211, D_210), D_210, E_209)) | ~m1_subset_1(k3_tmap_1(A_208, B_212, k1_tsep_1(A_208, C_211, D_210), C_211, E_209), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_211), u1_struct_0(B_212)))) | ~v5_pre_topc(k3_tmap_1(A_208, B_212, k1_tsep_1(A_208, C_211, D_210), C_211, E_209), C_211, B_212) | ~v1_funct_2(k3_tmap_1(A_208, B_212, k1_tsep_1(A_208, C_211, D_210), C_211, E_209), u1_struct_0(C_211), u1_struct_0(B_212)) | ~v1_funct_1(k3_tmap_1(A_208, B_212, k1_tsep_1(A_208, C_211, D_210), C_211, E_209)) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_208, C_211, D_210)), u1_struct_0(B_212)))) | ~v1_funct_2(E_209, u1_struct_0(k1_tsep_1(A_208, C_211, D_210)), u1_struct_0(B_212)) | ~v1_funct_1(E_209) | ~r4_tsep_1(A_208, C_211, D_210) | ~m1_pre_topc(D_210, A_208) | v2_struct_0(D_210) | ~m1_pre_topc(C_211, A_208) | v2_struct_0(C_211) | ~l1_pre_topc(B_212) | ~v2_pre_topc(B_212) | v2_struct_0(B_212) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.53/2.50  tff(c_859, plain, (![E_209, B_212]: (v5_pre_topc(E_209, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_212) | ~m1_subset_1(k3_tmap_1('#skF_1', B_212, '#skF_1', '#skF_5', E_209), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_212)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_212, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_209), '#skF_5', B_212) | ~v1_funct_2(k3_tmap_1('#skF_1', B_212, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_209), u1_struct_0('#skF_5'), u1_struct_0(B_212)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_212, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_209)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_212, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_209), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_212)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_212, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_209), '#skF_4', B_212) | ~v1_funct_2(k3_tmap_1('#skF_1', B_212, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_209), u1_struct_0('#skF_4'), u1_struct_0(B_212)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_212, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_209)) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_212)))) | ~v1_funct_2(E_209, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_212)) | ~v1_funct_1(E_209) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_212) | ~v2_pre_topc(B_212) | v2_struct_0(B_212) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_852])).
% 7.53/2.50  tff(c_863, plain, (![E_209, B_212]: (v5_pre_topc(E_209, '#skF_1', B_212) | ~m1_subset_1(k3_tmap_1('#skF_1', B_212, '#skF_1', '#skF_5', E_209), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_212)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_212, '#skF_1', '#skF_5', E_209), '#skF_5', B_212) | ~v1_funct_2(k3_tmap_1('#skF_1', B_212, '#skF_1', '#skF_5', E_209), u1_struct_0('#skF_5'), u1_struct_0(B_212)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_212, '#skF_1', '#skF_5', E_209)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_212, '#skF_1', '#skF_4', E_209), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_212)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_212, '#skF_1', '#skF_4', E_209), '#skF_4', B_212) | ~v1_funct_2(k3_tmap_1('#skF_1', B_212, '#skF_1', '#skF_4', E_209), u1_struct_0('#skF_4'), u1_struct_0(B_212)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_212, '#skF_1', '#skF_4', E_209)) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_212)))) | ~v1_funct_2(E_209, u1_struct_0('#skF_1'), u1_struct_0(B_212)) | ~v1_funct_1(E_209) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_212) | ~v2_pre_topc(B_212) | v2_struct_0(B_212) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_40, c_36, c_38, c_38, c_38, c_38, c_38, c_38, c_38, c_38, c_38, c_38, c_859])).
% 7.53/2.50  tff(c_888, plain, (![E_233, B_234]: (v5_pre_topc(E_233, '#skF_1', B_234) | ~m1_subset_1(k3_tmap_1('#skF_1', B_234, '#skF_1', '#skF_5', E_233), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_234)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_234, '#skF_1', '#skF_5', E_233), '#skF_5', B_234) | ~v1_funct_2(k3_tmap_1('#skF_1', B_234, '#skF_1', '#skF_5', E_233), u1_struct_0('#skF_5'), u1_struct_0(B_234)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_234, '#skF_1', '#skF_5', E_233)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_234, '#skF_1', '#skF_4', E_233), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_234)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_234, '#skF_1', '#skF_4', E_233), '#skF_4', B_234) | ~v1_funct_2(k3_tmap_1('#skF_1', B_234, '#skF_1', '#skF_4', E_233), u1_struct_0('#skF_4'), u1_struct_0(B_234)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_234, '#skF_1', '#skF_4', E_233)) | ~m1_subset_1(E_233, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_234)))) | ~v1_funct_2(E_233, u1_struct_0('#skF_1'), u1_struct_0(B_234)) | ~v1_funct_1(E_233) | ~l1_pre_topc(B_234) | ~v2_pre_topc(B_234) | v2_struct_0(B_234))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_863])).
% 7.53/2.50  tff(c_894, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), '#skF_5', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_341, c_888])).
% 7.53/2.50  tff(c_897, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_190, c_377, c_193, c_377, c_192, c_377, c_196, c_377, c_189, c_341, c_194, c_341, c_191, c_341, c_195, c_894])).
% 7.53/2.50  tff(c_899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_654, c_897])).
% 7.53/2.50  tff(c_901, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_120])).
% 7.53/2.50  tff(c_900, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_120])).
% 7.53/2.50  tff(c_925, plain, (![A_244, B_245, C_246, D_247]: (k2_partfun1(u1_struct_0(A_244), u1_struct_0(B_245), C_246, u1_struct_0(D_247))=k2_tmap_1(A_244, B_245, C_246, D_247) | ~m1_pre_topc(D_247, A_244) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_244), u1_struct_0(B_245)))) | ~v1_funct_2(C_246, u1_struct_0(A_244), u1_struct_0(B_245)) | ~v1_funct_1(C_246) | ~l1_pre_topc(B_245) | ~v2_pre_topc(B_245) | v2_struct_0(B_245) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.53/2.50  tff(c_929, plain, (![D_247]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_247))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_247) | ~m1_pre_topc(D_247, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_925])).
% 7.53/2.50  tff(c_936, plain, (![D_247]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_247))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_247) | ~m1_pre_topc(D_247, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_929])).
% 7.53/2.50  tff(c_937, plain, (![D_247]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_247))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_247) | ~m1_pre_topc(D_247, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_936])).
% 7.53/2.50  tff(c_916, plain, (![A_241, B_242, C_243]: (m1_pre_topc(k1_tsep_1(A_241, B_242, C_243), A_241) | ~m1_pre_topc(C_243, A_241) | v2_struct_0(C_243) | ~m1_pre_topc(B_242, A_241) | v2_struct_0(B_242) | ~l1_pre_topc(A_241) | v2_struct_0(A_241))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.50  tff(c_919, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_916])).
% 7.53/2.50  tff(c_921, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44, c_40, c_919])).
% 7.53/2.50  tff(c_922, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_921])).
% 7.53/2.50  tff(c_948, plain, (![C_252, B_249, D_251, A_253, E_250]: (k3_tmap_1(A_253, B_249, C_252, D_251, E_250)=k2_partfun1(u1_struct_0(C_252), u1_struct_0(B_249), E_250, u1_struct_0(D_251)) | ~m1_pre_topc(D_251, C_252) | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_252), u1_struct_0(B_249)))) | ~v1_funct_2(E_250, u1_struct_0(C_252), u1_struct_0(B_249)) | ~v1_funct_1(E_250) | ~m1_pre_topc(D_251, A_253) | ~m1_pre_topc(C_252, A_253) | ~l1_pre_topc(B_249) | ~v2_pre_topc(B_249) | v2_struct_0(B_249) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.53/2.50  tff(c_952, plain, (![A_253, D_251]: (k3_tmap_1(A_253, '#skF_2', '#skF_1', D_251, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_251)) | ~m1_pre_topc(D_251, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_251, A_253) | ~m1_pre_topc('#skF_1', A_253) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(resolution, [status(thm)], [c_48, c_948])).
% 7.53/2.50  tff(c_959, plain, (![A_253, D_251]: (k3_tmap_1(A_253, '#skF_2', '#skF_1', D_251, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_251)) | ~m1_pre_topc(D_251, '#skF_1') | ~m1_pre_topc(D_251, A_253) | ~m1_pre_topc('#skF_1', A_253) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_952])).
% 7.53/2.50  tff(c_967, plain, (![A_259, D_260]: (k3_tmap_1(A_259, '#skF_2', '#skF_1', D_260, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_260)) | ~m1_pre_topc(D_260, '#skF_1') | ~m1_pre_topc(D_260, A_259) | ~m1_pre_topc('#skF_1', A_259) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(negUnitSimplification, [status(thm)], [c_58, c_959])).
% 7.53/2.50  tff(c_973, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_967])).
% 7.53/2.50  tff(c_983, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_922, c_44, c_973])).
% 7.53/2.50  tff(c_984, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_983])).
% 7.53/2.50  tff(c_1015, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_937, c_984])).
% 7.53/2.50  tff(c_1021, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1015])).
% 7.53/2.50  tff(c_1384, plain, (![C_323, D_322, A_320, B_324, E_321]: (m1_subset_1(k3_tmap_1(A_320, B_324, k1_tsep_1(A_320, C_323, D_322), C_323, E_321), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_323), u1_struct_0(B_324)))) | ~v5_pre_topc(E_321, k1_tsep_1(A_320, C_323, D_322), B_324) | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_320, C_323, D_322)), u1_struct_0(B_324)))) | ~v1_funct_2(E_321, u1_struct_0(k1_tsep_1(A_320, C_323, D_322)), u1_struct_0(B_324)) | ~v1_funct_1(E_321) | ~r4_tsep_1(A_320, C_323, D_322) | ~m1_pre_topc(D_322, A_320) | v2_struct_0(D_322) | ~m1_pre_topc(C_323, A_320) | v2_struct_0(C_323) | ~l1_pre_topc(B_324) | ~v2_pre_topc(B_324) | v2_struct_0(B_324) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320) | v2_struct_0(A_320))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.53/2.50  tff(c_1429, plain, (![B_324, E_321]: (m1_subset_1(k3_tmap_1('#skF_1', B_324, '#skF_1', '#skF_4', E_321), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_324)))) | ~v5_pre_topc(E_321, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_324) | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_324)))) | ~v1_funct_2(E_321, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_324)) | ~v1_funct_1(E_321) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_324) | ~v2_pre_topc(B_324) | v2_struct_0(B_324) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1384])).
% 7.53/2.50  tff(c_1457, plain, (![B_324, E_321]: (m1_subset_1(k3_tmap_1('#skF_1', B_324, '#skF_1', '#skF_4', E_321), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_324)))) | ~v5_pre_topc(E_321, '#skF_1', B_324) | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_324)))) | ~v1_funct_2(E_321, u1_struct_0('#skF_1'), u1_struct_0(B_324)) | ~v1_funct_1(E_321) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_324) | ~v2_pre_topc(B_324) | v2_struct_0(B_324) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_40, c_36, c_38, c_38, c_38, c_1429])).
% 7.53/2.50  tff(c_1459, plain, (![B_325, E_326]: (m1_subset_1(k3_tmap_1('#skF_1', B_325, '#skF_1', '#skF_4', E_326), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_325)))) | ~v5_pre_topc(E_326, '#skF_1', B_325) | ~m1_subset_1(E_326, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_325)))) | ~v1_funct_2(E_326, u1_struct_0('#skF_1'), u1_struct_0(B_325)) | ~v1_funct_1(E_326) | ~l1_pre_topc(B_325) | ~v2_pre_topc(B_325) | v2_struct_0(B_325))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_1457])).
% 7.53/2.50  tff(c_1466, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1021, c_1459])).
% 7.53/2.50  tff(c_1472, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_900, c_1466])).
% 7.53/2.50  tff(c_1474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_901, c_1472])).
% 7.53/2.50  tff(c_1476, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_80])).
% 7.53/2.50  tff(c_1475, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_80])).
% 7.53/2.50  tff(c_1492, plain, (![A_333, B_334, C_335]: (m1_pre_topc(k1_tsep_1(A_333, B_334, C_335), A_333) | ~m1_pre_topc(C_335, A_333) | v2_struct_0(C_335) | ~m1_pre_topc(B_334, A_333) | v2_struct_0(B_334) | ~l1_pre_topc(A_333) | v2_struct_0(A_333))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.50  tff(c_1495, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_1492])).
% 7.53/2.50  tff(c_1497, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44, c_40, c_1495])).
% 7.53/2.50  tff(c_1498, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_1497])).
% 7.53/2.50  tff(c_1515, plain, (![B_341, E_342, D_343, C_344, A_345]: (k3_tmap_1(A_345, B_341, C_344, D_343, E_342)=k2_partfun1(u1_struct_0(C_344), u1_struct_0(B_341), E_342, u1_struct_0(D_343)) | ~m1_pre_topc(D_343, C_344) | ~m1_subset_1(E_342, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_344), u1_struct_0(B_341)))) | ~v1_funct_2(E_342, u1_struct_0(C_344), u1_struct_0(B_341)) | ~v1_funct_1(E_342) | ~m1_pre_topc(D_343, A_345) | ~m1_pre_topc(C_344, A_345) | ~l1_pre_topc(B_341) | ~v2_pre_topc(B_341) | v2_struct_0(B_341) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.53/2.50  tff(c_1517, plain, (![A_345, D_343]: (k3_tmap_1(A_345, '#skF_2', '#skF_1', D_343, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_343)) | ~m1_pre_topc(D_343, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_343, A_345) | ~m1_pre_topc('#skF_1', A_345) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(resolution, [status(thm)], [c_48, c_1515])).
% 7.53/2.50  tff(c_1520, plain, (![A_345, D_343]: (k3_tmap_1(A_345, '#skF_2', '#skF_1', D_343, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_343)) | ~m1_pre_topc(D_343, '#skF_1') | ~m1_pre_topc(D_343, A_345) | ~m1_pre_topc('#skF_1', A_345) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_1517])).
% 7.53/2.50  tff(c_1522, plain, (![A_346, D_347]: (k3_tmap_1(A_346, '#skF_2', '#skF_1', D_347, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_347)) | ~m1_pre_topc(D_347, '#skF_1') | ~m1_pre_topc(D_347, A_346) | ~m1_pre_topc('#skF_1', A_346) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346))), inference(negUnitSimplification, [status(thm)], [c_58, c_1520])).
% 7.53/2.50  tff(c_1530, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1522])).
% 7.53/2.50  tff(c_1542, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1498, c_40, c_1530])).
% 7.53/2.50  tff(c_1543, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_1542])).
% 7.53/2.50  tff(c_1499, plain, (![A_336, B_337, C_338, D_339]: (k2_partfun1(u1_struct_0(A_336), u1_struct_0(B_337), C_338, u1_struct_0(D_339))=k2_tmap_1(A_336, B_337, C_338, D_339) | ~m1_pre_topc(D_339, A_336) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_336), u1_struct_0(B_337)))) | ~v1_funct_2(C_338, u1_struct_0(A_336), u1_struct_0(B_337)) | ~v1_funct_1(C_338) | ~l1_pre_topc(B_337) | ~v2_pre_topc(B_337) | v2_struct_0(B_337) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.53/2.50  tff(c_1501, plain, (![D_339]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_339))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_339) | ~m1_pre_topc(D_339, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_1499])).
% 7.53/2.50  tff(c_1504, plain, (![D_339]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_339))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_339) | ~m1_pre_topc(D_339, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_1501])).
% 7.53/2.50  tff(c_1505, plain, (![D_339]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_339))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_339) | ~m1_pre_topc(D_339, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_1504])).
% 7.53/2.50  tff(c_1589, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1543, c_1505])).
% 7.53/2.50  tff(c_1596, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1589])).
% 7.53/2.50  tff(c_1881, plain, (![A_405, C_408, D_407, E_406, B_409]: (m1_subset_1(k3_tmap_1(A_405, B_409, k1_tsep_1(A_405, C_408, D_407), D_407, E_406), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_407), u1_struct_0(B_409)))) | ~v5_pre_topc(E_406, k1_tsep_1(A_405, C_408, D_407), B_409) | ~m1_subset_1(E_406, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_405, C_408, D_407)), u1_struct_0(B_409)))) | ~v1_funct_2(E_406, u1_struct_0(k1_tsep_1(A_405, C_408, D_407)), u1_struct_0(B_409)) | ~v1_funct_1(E_406) | ~r4_tsep_1(A_405, C_408, D_407) | ~m1_pre_topc(D_407, A_405) | v2_struct_0(D_407) | ~m1_pre_topc(C_408, A_405) | v2_struct_0(C_408) | ~l1_pre_topc(B_409) | ~v2_pre_topc(B_409) | v2_struct_0(B_409) | ~l1_pre_topc(A_405) | ~v2_pre_topc(A_405) | v2_struct_0(A_405))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.53/2.50  tff(c_1926, plain, (![B_409, E_406]: (m1_subset_1(k3_tmap_1('#skF_1', B_409, '#skF_1', '#skF_5', E_406), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_409)))) | ~v5_pre_topc(E_406, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_409) | ~m1_subset_1(E_406, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_409)))) | ~v1_funct_2(E_406, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_409)) | ~v1_funct_1(E_406) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_409) | ~v2_pre_topc(B_409) | v2_struct_0(B_409) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1881])).
% 7.53/2.50  tff(c_1954, plain, (![B_409, E_406]: (m1_subset_1(k3_tmap_1('#skF_1', B_409, '#skF_1', '#skF_5', E_406), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_409)))) | ~v5_pre_topc(E_406, '#skF_1', B_409) | ~m1_subset_1(E_406, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_409)))) | ~v1_funct_2(E_406, u1_struct_0('#skF_1'), u1_struct_0(B_409)) | ~v1_funct_1(E_406) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_409) | ~v2_pre_topc(B_409) | v2_struct_0(B_409) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_40, c_36, c_38, c_38, c_38, c_1926])).
% 7.53/2.50  tff(c_1999, plain, (![B_414, E_415]: (m1_subset_1(k3_tmap_1('#skF_1', B_414, '#skF_1', '#skF_5', E_415), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(B_414)))) | ~v5_pre_topc(E_415, '#skF_1', B_414) | ~m1_subset_1(E_415, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_414)))) | ~v1_funct_2(E_415, u1_struct_0('#skF_1'), u1_struct_0(B_414)) | ~v1_funct_1(E_415) | ~l1_pre_topc(B_414) | ~v2_pre_topc(B_414) | v2_struct_0(B_414))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_1954])).
% 7.53/2.50  tff(c_2006, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1596, c_1999])).
% 7.53/2.50  tff(c_2012, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_1475, c_2006])).
% 7.53/2.50  tff(c_2014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1476, c_2012])).
% 7.53/2.50  tff(c_2016, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_100])).
% 7.53/2.50  tff(c_2015, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_100])).
% 7.53/2.50  tff(c_2035, plain, (![A_422, B_423, C_424]: (m1_pre_topc(k1_tsep_1(A_422, B_423, C_424), A_422) | ~m1_pre_topc(C_424, A_422) | v2_struct_0(C_424) | ~m1_pre_topc(B_423, A_422) | v2_struct_0(B_423) | ~l1_pre_topc(A_422) | v2_struct_0(A_422))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.50  tff(c_2038, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2035])).
% 7.53/2.50  tff(c_2040, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44, c_40, c_2038])).
% 7.53/2.50  tff(c_2041, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_2040])).
% 7.53/2.50  tff(c_2058, plain, (![D_432, E_431, A_434, C_433, B_430]: (k3_tmap_1(A_434, B_430, C_433, D_432, E_431)=k2_partfun1(u1_struct_0(C_433), u1_struct_0(B_430), E_431, u1_struct_0(D_432)) | ~m1_pre_topc(D_432, C_433) | ~m1_subset_1(E_431, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_433), u1_struct_0(B_430)))) | ~v1_funct_2(E_431, u1_struct_0(C_433), u1_struct_0(B_430)) | ~v1_funct_1(E_431) | ~m1_pre_topc(D_432, A_434) | ~m1_pre_topc(C_433, A_434) | ~l1_pre_topc(B_430) | ~v2_pre_topc(B_430) | v2_struct_0(B_430) | ~l1_pre_topc(A_434) | ~v2_pre_topc(A_434) | v2_struct_0(A_434))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.53/2.50  tff(c_2060, plain, (![A_434, D_432]: (k3_tmap_1(A_434, '#skF_2', '#skF_1', D_432, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_432)) | ~m1_pre_topc(D_432, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_432, A_434) | ~m1_pre_topc('#skF_1', A_434) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_434) | ~v2_pre_topc(A_434) | v2_struct_0(A_434))), inference(resolution, [status(thm)], [c_48, c_2058])).
% 7.53/2.50  tff(c_2063, plain, (![A_434, D_432]: (k3_tmap_1(A_434, '#skF_2', '#skF_1', D_432, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_432)) | ~m1_pre_topc(D_432, '#skF_1') | ~m1_pre_topc(D_432, A_434) | ~m1_pre_topc('#skF_1', A_434) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_434) | ~v2_pre_topc(A_434) | v2_struct_0(A_434))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2060])).
% 7.53/2.50  tff(c_2071, plain, (![A_440, D_441]: (k3_tmap_1(A_440, '#skF_2', '#skF_1', D_441, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_441)) | ~m1_pre_topc(D_441, '#skF_1') | ~m1_pre_topc(D_441, A_440) | ~m1_pre_topc('#skF_1', A_440) | ~l1_pre_topc(A_440) | ~v2_pre_topc(A_440) | v2_struct_0(A_440))), inference(negUnitSimplification, [status(thm)], [c_58, c_2063])).
% 7.53/2.50  tff(c_2079, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2071])).
% 7.53/2.50  tff(c_2091, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2041, c_40, c_2079])).
% 7.53/2.50  tff(c_2092, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_2091])).
% 7.53/2.50  tff(c_2042, plain, (![A_425, B_426, C_427, D_428]: (k2_partfun1(u1_struct_0(A_425), u1_struct_0(B_426), C_427, u1_struct_0(D_428))=k2_tmap_1(A_425, B_426, C_427, D_428) | ~m1_pre_topc(D_428, A_425) | ~m1_subset_1(C_427, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_425), u1_struct_0(B_426)))) | ~v1_funct_2(C_427, u1_struct_0(A_425), u1_struct_0(B_426)) | ~v1_funct_1(C_427) | ~l1_pre_topc(B_426) | ~v2_pre_topc(B_426) | v2_struct_0(B_426) | ~l1_pre_topc(A_425) | ~v2_pre_topc(A_425) | v2_struct_0(A_425))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.53/2.50  tff(c_2044, plain, (![D_428]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_428))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_428) | ~m1_pre_topc(D_428, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_2042])).
% 7.53/2.50  tff(c_2047, plain, (![D_428]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_428))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_428) | ~m1_pre_topc(D_428, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_2044])).
% 7.53/2.50  tff(c_2048, plain, (![D_428]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_428))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_428) | ~m1_pre_topc(D_428, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_2047])).
% 7.53/2.50  tff(c_2174, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2092, c_2048])).
% 7.53/2.50  tff(c_2181, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2174])).
% 7.53/2.50  tff(c_2321, plain, (![E_476, B_479, A_475, C_478, D_477]: (v1_funct_2(k3_tmap_1(A_475, B_479, k1_tsep_1(A_475, C_478, D_477), D_477, E_476), u1_struct_0(D_477), u1_struct_0(B_479)) | ~v5_pre_topc(E_476, k1_tsep_1(A_475, C_478, D_477), B_479) | ~m1_subset_1(E_476, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_475, C_478, D_477)), u1_struct_0(B_479)))) | ~v1_funct_2(E_476, u1_struct_0(k1_tsep_1(A_475, C_478, D_477)), u1_struct_0(B_479)) | ~v1_funct_1(E_476) | ~r4_tsep_1(A_475, C_478, D_477) | ~m1_pre_topc(D_477, A_475) | v2_struct_0(D_477) | ~m1_pre_topc(C_478, A_475) | v2_struct_0(C_478) | ~l1_pre_topc(B_479) | ~v2_pre_topc(B_479) | v2_struct_0(B_479) | ~l1_pre_topc(A_475) | ~v2_pre_topc(A_475) | v2_struct_0(A_475))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.53/2.50  tff(c_2323, plain, (![B_479, E_476]: (v1_funct_2(k3_tmap_1('#skF_1', B_479, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_476), u1_struct_0('#skF_5'), u1_struct_0(B_479)) | ~v5_pre_topc(E_476, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_479) | ~m1_subset_1(E_476, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_479)))) | ~v1_funct_2(E_476, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_479)) | ~v1_funct_1(E_476) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_479) | ~v2_pre_topc(B_479) | v2_struct_0(B_479) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2321])).
% 7.53/2.50  tff(c_2325, plain, (![B_479, E_476]: (v1_funct_2(k3_tmap_1('#skF_1', B_479, '#skF_1', '#skF_5', E_476), u1_struct_0('#skF_5'), u1_struct_0(B_479)) | ~v5_pre_topc(E_476, '#skF_1', B_479) | ~m1_subset_1(E_476, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_479)))) | ~v1_funct_2(E_476, u1_struct_0('#skF_1'), u1_struct_0(B_479)) | ~v1_funct_1(E_476) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_479) | ~v2_pre_topc(B_479) | v2_struct_0(B_479) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_40, c_36, c_38, c_38, c_38, c_2323])).
% 7.53/2.50  tff(c_2327, plain, (![B_480, E_481]: (v1_funct_2(k3_tmap_1('#skF_1', B_480, '#skF_1', '#skF_5', E_481), u1_struct_0('#skF_5'), u1_struct_0(B_480)) | ~v5_pre_topc(E_481, '#skF_1', B_480) | ~m1_subset_1(E_481, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_480)))) | ~v1_funct_2(E_481, u1_struct_0('#skF_1'), u1_struct_0(B_480)) | ~v1_funct_1(E_481) | ~l1_pre_topc(B_480) | ~v2_pre_topc(B_480) | v2_struct_0(B_480))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_2325])).
% 7.53/2.50  tff(c_2329, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_2327])).
% 7.53/2.50  tff(c_2332, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2015, c_2181, c_2329])).
% 7.53/2.50  tff(c_2334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2016, c_2332])).
% 7.53/2.50  tff(c_2336, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_140])).
% 7.53/2.50  tff(c_2335, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_140])).
% 7.53/2.50  tff(c_2356, plain, (![A_488, B_489, C_490]: (m1_pre_topc(k1_tsep_1(A_488, B_489, C_490), A_488) | ~m1_pre_topc(C_490, A_488) | v2_struct_0(C_490) | ~m1_pre_topc(B_489, A_488) | v2_struct_0(B_489) | ~l1_pre_topc(A_488) | v2_struct_0(A_488))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.50  tff(c_2359, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2356])).
% 7.53/2.50  tff(c_2361, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44, c_40, c_2359])).
% 7.53/2.50  tff(c_2362, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_2361])).
% 7.53/2.50  tff(c_2370, plain, (![D_497, C_498, A_499, E_496, B_495]: (k3_tmap_1(A_499, B_495, C_498, D_497, E_496)=k2_partfun1(u1_struct_0(C_498), u1_struct_0(B_495), E_496, u1_struct_0(D_497)) | ~m1_pre_topc(D_497, C_498) | ~m1_subset_1(E_496, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_498), u1_struct_0(B_495)))) | ~v1_funct_2(E_496, u1_struct_0(C_498), u1_struct_0(B_495)) | ~v1_funct_1(E_496) | ~m1_pre_topc(D_497, A_499) | ~m1_pre_topc(C_498, A_499) | ~l1_pre_topc(B_495) | ~v2_pre_topc(B_495) | v2_struct_0(B_495) | ~l1_pre_topc(A_499) | ~v2_pre_topc(A_499) | v2_struct_0(A_499))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.53/2.50  tff(c_2372, plain, (![A_499, D_497]: (k3_tmap_1(A_499, '#skF_2', '#skF_1', D_497, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_497)) | ~m1_pre_topc(D_497, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_497, A_499) | ~m1_pre_topc('#skF_1', A_499) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_499) | ~v2_pre_topc(A_499) | v2_struct_0(A_499))), inference(resolution, [status(thm)], [c_48, c_2370])).
% 7.53/2.50  tff(c_2375, plain, (![A_499, D_497]: (k3_tmap_1(A_499, '#skF_2', '#skF_1', D_497, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_497)) | ~m1_pre_topc(D_497, '#skF_1') | ~m1_pre_topc(D_497, A_499) | ~m1_pre_topc('#skF_1', A_499) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_499) | ~v2_pre_topc(A_499) | v2_struct_0(A_499))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2372])).
% 7.53/2.50  tff(c_2386, plain, (![A_501, D_502]: (k3_tmap_1(A_501, '#skF_2', '#skF_1', D_502, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_502)) | ~m1_pre_topc(D_502, '#skF_1') | ~m1_pre_topc(D_502, A_501) | ~m1_pre_topc('#skF_1', A_501) | ~l1_pre_topc(A_501) | ~v2_pre_topc(A_501) | v2_struct_0(A_501))), inference(negUnitSimplification, [status(thm)], [c_58, c_2375])).
% 7.53/2.50  tff(c_2392, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2386])).
% 7.53/2.50  tff(c_2402, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2362, c_44, c_2392])).
% 7.53/2.50  tff(c_2403, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_2402])).
% 7.53/2.50  tff(c_2363, plain, (![A_491, B_492, C_493, D_494]: (k2_partfun1(u1_struct_0(A_491), u1_struct_0(B_492), C_493, u1_struct_0(D_494))=k2_tmap_1(A_491, B_492, C_493, D_494) | ~m1_pre_topc(D_494, A_491) | ~m1_subset_1(C_493, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_491), u1_struct_0(B_492)))) | ~v1_funct_2(C_493, u1_struct_0(A_491), u1_struct_0(B_492)) | ~v1_funct_1(C_493) | ~l1_pre_topc(B_492) | ~v2_pre_topc(B_492) | v2_struct_0(B_492) | ~l1_pre_topc(A_491) | ~v2_pre_topc(A_491) | v2_struct_0(A_491))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.53/2.50  tff(c_2365, plain, (![D_494]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_494))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_494) | ~m1_pre_topc(D_494, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_2363])).
% 7.53/2.50  tff(c_2368, plain, (![D_494]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_494))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_494) | ~m1_pre_topc(D_494, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_2365])).
% 7.53/2.50  tff(c_2369, plain, (![D_494]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_494))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_494) | ~m1_pre_topc(D_494, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_2368])).
% 7.53/2.50  tff(c_2489, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2403, c_2369])).
% 7.53/2.50  tff(c_2496, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2489])).
% 7.53/2.50  tff(c_2642, plain, (![E_542, C_544, D_543, A_541, B_545]: (v1_funct_2(k3_tmap_1(A_541, B_545, k1_tsep_1(A_541, C_544, D_543), C_544, E_542), u1_struct_0(C_544), u1_struct_0(B_545)) | ~v5_pre_topc(E_542, k1_tsep_1(A_541, C_544, D_543), B_545) | ~m1_subset_1(E_542, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_541, C_544, D_543)), u1_struct_0(B_545)))) | ~v1_funct_2(E_542, u1_struct_0(k1_tsep_1(A_541, C_544, D_543)), u1_struct_0(B_545)) | ~v1_funct_1(E_542) | ~r4_tsep_1(A_541, C_544, D_543) | ~m1_pre_topc(D_543, A_541) | v2_struct_0(D_543) | ~m1_pre_topc(C_544, A_541) | v2_struct_0(C_544) | ~l1_pre_topc(B_545) | ~v2_pre_topc(B_545) | v2_struct_0(B_545) | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541) | v2_struct_0(A_541))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.53/2.50  tff(c_2644, plain, (![B_545, E_542]: (v1_funct_2(k3_tmap_1('#skF_1', B_545, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_542), u1_struct_0('#skF_4'), u1_struct_0(B_545)) | ~v5_pre_topc(E_542, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_545) | ~m1_subset_1(E_542, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_545)))) | ~v1_funct_2(E_542, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_545)) | ~v1_funct_1(E_542) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_545) | ~v2_pre_topc(B_545) | v2_struct_0(B_545) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2642])).
% 7.53/2.50  tff(c_2646, plain, (![B_545, E_542]: (v1_funct_2(k3_tmap_1('#skF_1', B_545, '#skF_1', '#skF_4', E_542), u1_struct_0('#skF_4'), u1_struct_0(B_545)) | ~v5_pre_topc(E_542, '#skF_1', B_545) | ~m1_subset_1(E_542, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_545)))) | ~v1_funct_2(E_542, u1_struct_0('#skF_1'), u1_struct_0(B_545)) | ~v1_funct_1(E_542) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_545) | ~v2_pre_topc(B_545) | v2_struct_0(B_545) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_40, c_36, c_38, c_38, c_38, c_2644])).
% 7.53/2.50  tff(c_2648, plain, (![B_546, E_547]: (v1_funct_2(k3_tmap_1('#skF_1', B_546, '#skF_1', '#skF_4', E_547), u1_struct_0('#skF_4'), u1_struct_0(B_546)) | ~v5_pre_topc(E_547, '#skF_1', B_546) | ~m1_subset_1(E_547, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_546)))) | ~v1_funct_2(E_547, u1_struct_0('#skF_1'), u1_struct_0(B_546)) | ~v1_funct_1(E_547) | ~l1_pre_topc(B_546) | ~v2_pre_topc(B_546) | v2_struct_0(B_546))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_2646])).
% 7.53/2.50  tff(c_2650, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_2648])).
% 7.53/2.50  tff(c_2653, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2335, c_2496, c_2650])).
% 7.53/2.50  tff(c_2655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2336, c_2653])).
% 7.53/2.50  tff(c_2657, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_130])).
% 7.53/2.50  tff(c_2656, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_130])).
% 7.53/2.50  tff(c_2676, plain, (![A_554, B_555, C_556]: (m1_pre_topc(k1_tsep_1(A_554, B_555, C_556), A_554) | ~m1_pre_topc(C_556, A_554) | v2_struct_0(C_556) | ~m1_pre_topc(B_555, A_554) | v2_struct_0(B_555) | ~l1_pre_topc(A_554) | v2_struct_0(A_554))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.50  tff(c_2679, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2676])).
% 7.53/2.50  tff(c_2681, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44, c_40, c_2679])).
% 7.53/2.50  tff(c_2682, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_2681])).
% 7.53/2.50  tff(c_2699, plain, (![D_564, A_566, C_565, B_562, E_563]: (k3_tmap_1(A_566, B_562, C_565, D_564, E_563)=k2_partfun1(u1_struct_0(C_565), u1_struct_0(B_562), E_563, u1_struct_0(D_564)) | ~m1_pre_topc(D_564, C_565) | ~m1_subset_1(E_563, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_565), u1_struct_0(B_562)))) | ~v1_funct_2(E_563, u1_struct_0(C_565), u1_struct_0(B_562)) | ~v1_funct_1(E_563) | ~m1_pre_topc(D_564, A_566) | ~m1_pre_topc(C_565, A_566) | ~l1_pre_topc(B_562) | ~v2_pre_topc(B_562) | v2_struct_0(B_562) | ~l1_pre_topc(A_566) | ~v2_pre_topc(A_566) | v2_struct_0(A_566))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.53/2.50  tff(c_2701, plain, (![A_566, D_564]: (k3_tmap_1(A_566, '#skF_2', '#skF_1', D_564, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_564)) | ~m1_pre_topc(D_564, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_564, A_566) | ~m1_pre_topc('#skF_1', A_566) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_566) | ~v2_pre_topc(A_566) | v2_struct_0(A_566))), inference(resolution, [status(thm)], [c_48, c_2699])).
% 7.53/2.50  tff(c_2704, plain, (![A_566, D_564]: (k3_tmap_1(A_566, '#skF_2', '#skF_1', D_564, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_564)) | ~m1_pre_topc(D_564, '#skF_1') | ~m1_pre_topc(D_564, A_566) | ~m1_pre_topc('#skF_1', A_566) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_566) | ~v2_pre_topc(A_566) | v2_struct_0(A_566))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2701])).
% 7.53/2.50  tff(c_2706, plain, (![A_567, D_568]: (k3_tmap_1(A_567, '#skF_2', '#skF_1', D_568, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_568)) | ~m1_pre_topc(D_568, '#skF_1') | ~m1_pre_topc(D_568, A_567) | ~m1_pre_topc('#skF_1', A_567) | ~l1_pre_topc(A_567) | ~v2_pre_topc(A_567) | v2_struct_0(A_567))), inference(negUnitSimplification, [status(thm)], [c_58, c_2704])).
% 7.53/2.50  tff(c_2712, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2706])).
% 7.53/2.50  tff(c_2722, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2682, c_44, c_2712])).
% 7.53/2.50  tff(c_2723, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_2722])).
% 7.53/2.50  tff(c_2683, plain, (![A_557, B_558, C_559, D_560]: (k2_partfun1(u1_struct_0(A_557), u1_struct_0(B_558), C_559, u1_struct_0(D_560))=k2_tmap_1(A_557, B_558, C_559, D_560) | ~m1_pre_topc(D_560, A_557) | ~m1_subset_1(C_559, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_557), u1_struct_0(B_558)))) | ~v1_funct_2(C_559, u1_struct_0(A_557), u1_struct_0(B_558)) | ~v1_funct_1(C_559) | ~l1_pre_topc(B_558) | ~v2_pre_topc(B_558) | v2_struct_0(B_558) | ~l1_pre_topc(A_557) | ~v2_pre_topc(A_557) | v2_struct_0(A_557))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.53/2.50  tff(c_2685, plain, (![D_560]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_560))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_560) | ~m1_pre_topc(D_560, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_2683])).
% 7.53/2.50  tff(c_2688, plain, (![D_560]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_560))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_560) | ~m1_pre_topc(D_560, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_2685])).
% 7.53/2.50  tff(c_2689, plain, (![D_560]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_560))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_560) | ~m1_pre_topc(D_560, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_2688])).
% 7.53/2.50  tff(c_2767, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2723, c_2689])).
% 7.53/2.50  tff(c_2774, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2767])).
% 7.53/2.50  tff(c_2949, plain, (![E_601, A_600, C_603, B_604, D_602]: (v5_pre_topc(k3_tmap_1(A_600, B_604, k1_tsep_1(A_600, C_603, D_602), C_603, E_601), C_603, B_604) | ~v5_pre_topc(E_601, k1_tsep_1(A_600, C_603, D_602), B_604) | ~m1_subset_1(E_601, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_600, C_603, D_602)), u1_struct_0(B_604)))) | ~v1_funct_2(E_601, u1_struct_0(k1_tsep_1(A_600, C_603, D_602)), u1_struct_0(B_604)) | ~v1_funct_1(E_601) | ~r4_tsep_1(A_600, C_603, D_602) | ~m1_pre_topc(D_602, A_600) | v2_struct_0(D_602) | ~m1_pre_topc(C_603, A_600) | v2_struct_0(C_603) | ~l1_pre_topc(B_604) | ~v2_pre_topc(B_604) | v2_struct_0(B_604) | ~l1_pre_topc(A_600) | ~v2_pre_topc(A_600) | v2_struct_0(A_600))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.53/2.50  tff(c_2951, plain, (![B_604, E_601]: (v5_pre_topc(k3_tmap_1('#skF_1', B_604, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_601), '#skF_4', B_604) | ~v5_pre_topc(E_601, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_604) | ~m1_subset_1(E_601, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_604)))) | ~v1_funct_2(E_601, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_604)) | ~v1_funct_1(E_601) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_604) | ~v2_pre_topc(B_604) | v2_struct_0(B_604) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2949])).
% 7.53/2.50  tff(c_2953, plain, (![B_604, E_601]: (v5_pre_topc(k3_tmap_1('#skF_1', B_604, '#skF_1', '#skF_4', E_601), '#skF_4', B_604) | ~v5_pre_topc(E_601, '#skF_1', B_604) | ~m1_subset_1(E_601, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_604)))) | ~v1_funct_2(E_601, u1_struct_0('#skF_1'), u1_struct_0(B_604)) | ~v1_funct_1(E_601) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_604) | ~v2_pre_topc(B_604) | v2_struct_0(B_604) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_40, c_36, c_38, c_38, c_38, c_2951])).
% 7.53/2.50  tff(c_2955, plain, (![B_605, E_606]: (v5_pre_topc(k3_tmap_1('#skF_1', B_605, '#skF_1', '#skF_4', E_606), '#skF_4', B_605) | ~v5_pre_topc(E_606, '#skF_1', B_605) | ~m1_subset_1(E_606, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_605)))) | ~v1_funct_2(E_606, u1_struct_0('#skF_1'), u1_struct_0(B_605)) | ~v1_funct_1(E_606) | ~l1_pre_topc(B_605) | ~v2_pre_topc(B_605) | v2_struct_0(B_605))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_2953])).
% 7.53/2.50  tff(c_2957, plain, (v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_2955])).
% 7.53/2.50  tff(c_2960, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2656, c_2774, c_2957])).
% 7.53/2.50  tff(c_2962, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2657, c_2960])).
% 7.53/2.50  tff(c_2964, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_90])).
% 7.53/2.50  tff(c_2963, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_90])).
% 7.53/2.50  tff(c_2984, plain, (![A_613, B_614, C_615]: (m1_pre_topc(k1_tsep_1(A_613, B_614, C_615), A_613) | ~m1_pre_topc(C_615, A_613) | v2_struct_0(C_615) | ~m1_pre_topc(B_614, A_613) | v2_struct_0(B_614) | ~l1_pre_topc(A_613) | v2_struct_0(A_613))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.50  tff(c_2987, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2984])).
% 7.53/2.50  tff(c_2989, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44, c_40, c_2987])).
% 7.53/2.50  tff(c_2990, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_2989])).
% 7.53/2.50  tff(c_3009, plain, (![D_623, A_625, E_622, C_624, B_621]: (k3_tmap_1(A_625, B_621, C_624, D_623, E_622)=k2_partfun1(u1_struct_0(C_624), u1_struct_0(B_621), E_622, u1_struct_0(D_623)) | ~m1_pre_topc(D_623, C_624) | ~m1_subset_1(E_622, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_624), u1_struct_0(B_621)))) | ~v1_funct_2(E_622, u1_struct_0(C_624), u1_struct_0(B_621)) | ~v1_funct_1(E_622) | ~m1_pre_topc(D_623, A_625) | ~m1_pre_topc(C_624, A_625) | ~l1_pre_topc(B_621) | ~v2_pre_topc(B_621) | v2_struct_0(B_621) | ~l1_pre_topc(A_625) | ~v2_pre_topc(A_625) | v2_struct_0(A_625))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.53/2.50  tff(c_3011, plain, (![A_625, D_623]: (k3_tmap_1(A_625, '#skF_2', '#skF_1', D_623, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_623)) | ~m1_pre_topc(D_623, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_623, A_625) | ~m1_pre_topc('#skF_1', A_625) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_625) | ~v2_pre_topc(A_625) | v2_struct_0(A_625))), inference(resolution, [status(thm)], [c_48, c_3009])).
% 7.53/2.50  tff(c_3014, plain, (![A_625, D_623]: (k3_tmap_1(A_625, '#skF_2', '#skF_1', D_623, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_623)) | ~m1_pre_topc(D_623, '#skF_1') | ~m1_pre_topc(D_623, A_625) | ~m1_pre_topc('#skF_1', A_625) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_625) | ~v2_pre_topc(A_625) | v2_struct_0(A_625))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_3011])).
% 7.53/2.50  tff(c_3016, plain, (![A_626, D_627]: (k3_tmap_1(A_626, '#skF_2', '#skF_1', D_627, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_627)) | ~m1_pre_topc(D_627, '#skF_1') | ~m1_pre_topc(D_627, A_626) | ~m1_pre_topc('#skF_1', A_626) | ~l1_pre_topc(A_626) | ~v2_pre_topc(A_626) | v2_struct_0(A_626))), inference(negUnitSimplification, [status(thm)], [c_58, c_3014])).
% 7.53/2.50  tff(c_3024, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_3016])).
% 7.53/2.50  tff(c_3036, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2990, c_40, c_3024])).
% 7.53/2.50  tff(c_3037, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_3036])).
% 7.53/2.50  tff(c_2991, plain, (![A_616, B_617, C_618, D_619]: (k2_partfun1(u1_struct_0(A_616), u1_struct_0(B_617), C_618, u1_struct_0(D_619))=k2_tmap_1(A_616, B_617, C_618, D_619) | ~m1_pre_topc(D_619, A_616) | ~m1_subset_1(C_618, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_616), u1_struct_0(B_617)))) | ~v1_funct_2(C_618, u1_struct_0(A_616), u1_struct_0(B_617)) | ~v1_funct_1(C_618) | ~l1_pre_topc(B_617) | ~v2_pre_topc(B_617) | v2_struct_0(B_617) | ~l1_pre_topc(A_616) | ~v2_pre_topc(A_616) | v2_struct_0(A_616))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.53/2.50  tff(c_2993, plain, (![D_619]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_619))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_619) | ~m1_pre_topc(D_619, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_2991])).
% 7.53/2.50  tff(c_2996, plain, (![D_619]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_619))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_619) | ~m1_pre_topc(D_619, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_2993])).
% 7.53/2.50  tff(c_2997, plain, (![D_619]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_619))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_619) | ~m1_pre_topc(D_619, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_2996])).
% 7.53/2.50  tff(c_3083, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3037, c_2997])).
% 7.53/2.50  tff(c_3090, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3083])).
% 7.53/2.50  tff(c_3246, plain, (![C_655, B_656, A_652, D_654, E_653]: (v5_pre_topc(k3_tmap_1(A_652, B_656, k1_tsep_1(A_652, C_655, D_654), D_654, E_653), D_654, B_656) | ~v5_pre_topc(E_653, k1_tsep_1(A_652, C_655, D_654), B_656) | ~m1_subset_1(E_653, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_652, C_655, D_654)), u1_struct_0(B_656)))) | ~v1_funct_2(E_653, u1_struct_0(k1_tsep_1(A_652, C_655, D_654)), u1_struct_0(B_656)) | ~v1_funct_1(E_653) | ~r4_tsep_1(A_652, C_655, D_654) | ~m1_pre_topc(D_654, A_652) | v2_struct_0(D_654) | ~m1_pre_topc(C_655, A_652) | v2_struct_0(C_655) | ~l1_pre_topc(B_656) | ~v2_pre_topc(B_656) | v2_struct_0(B_656) | ~l1_pre_topc(A_652) | ~v2_pre_topc(A_652) | v2_struct_0(A_652))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.53/2.50  tff(c_3248, plain, (![B_656, E_653]: (v5_pre_topc(k3_tmap_1('#skF_1', B_656, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_653), '#skF_5', B_656) | ~v5_pre_topc(E_653, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_656) | ~m1_subset_1(E_653, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_656)))) | ~v1_funct_2(E_653, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_656)) | ~v1_funct_1(E_653) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_656) | ~v2_pre_topc(B_656) | v2_struct_0(B_656) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3246])).
% 7.53/2.50  tff(c_3250, plain, (![B_656, E_653]: (v5_pre_topc(k3_tmap_1('#skF_1', B_656, '#skF_1', '#skF_5', E_653), '#skF_5', B_656) | ~v5_pre_topc(E_653, '#skF_1', B_656) | ~m1_subset_1(E_653, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_656)))) | ~v1_funct_2(E_653, u1_struct_0('#skF_1'), u1_struct_0(B_656)) | ~v1_funct_1(E_653) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_656) | ~v2_pre_topc(B_656) | v2_struct_0(B_656) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_40, c_36, c_38, c_38, c_38, c_3248])).
% 7.53/2.50  tff(c_3252, plain, (![B_657, E_658]: (v5_pre_topc(k3_tmap_1('#skF_1', B_657, '#skF_1', '#skF_5', E_658), '#skF_5', B_657) | ~v5_pre_topc(E_658, '#skF_1', B_657) | ~m1_subset_1(E_658, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_657)))) | ~v1_funct_2(E_658, u1_struct_0('#skF_1'), u1_struct_0(B_657)) | ~v1_funct_1(E_658) | ~l1_pre_topc(B_657) | ~v2_pre_topc(B_657) | v2_struct_0(B_657))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_3250])).
% 7.53/2.50  tff(c_3254, plain, (v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), '#skF_5', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_3252])).
% 7.53/2.50  tff(c_3257, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2963, c_3090, c_3254])).
% 7.53/2.50  tff(c_3259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2964, c_3257])).
% 7.53/2.50  tff(c_3261, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_150])).
% 7.53/2.50  tff(c_3260, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_150])).
% 7.53/2.50  tff(c_3282, plain, (![A_665, B_666, C_667]: (m1_pre_topc(k1_tsep_1(A_665, B_666, C_667), A_665) | ~m1_pre_topc(C_667, A_665) | v2_struct_0(C_667) | ~m1_pre_topc(B_666, A_665) | v2_struct_0(B_666) | ~l1_pre_topc(A_665) | v2_struct_0(A_665))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.50  tff(c_3285, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_3282])).
% 7.53/2.50  tff(c_3287, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44, c_40, c_3285])).
% 7.53/2.50  tff(c_3288, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_3287])).
% 7.53/2.50  tff(c_3305, plain, (![D_675, B_673, E_674, A_677, C_676]: (k3_tmap_1(A_677, B_673, C_676, D_675, E_674)=k2_partfun1(u1_struct_0(C_676), u1_struct_0(B_673), E_674, u1_struct_0(D_675)) | ~m1_pre_topc(D_675, C_676) | ~m1_subset_1(E_674, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_676), u1_struct_0(B_673)))) | ~v1_funct_2(E_674, u1_struct_0(C_676), u1_struct_0(B_673)) | ~v1_funct_1(E_674) | ~m1_pre_topc(D_675, A_677) | ~m1_pre_topc(C_676, A_677) | ~l1_pre_topc(B_673) | ~v2_pre_topc(B_673) | v2_struct_0(B_673) | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677) | v2_struct_0(A_677))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.53/2.50  tff(c_3307, plain, (![A_677, D_675]: (k3_tmap_1(A_677, '#skF_2', '#skF_1', D_675, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_675)) | ~m1_pre_topc(D_675, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_675, A_677) | ~m1_pre_topc('#skF_1', A_677) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677) | v2_struct_0(A_677))), inference(resolution, [status(thm)], [c_48, c_3305])).
% 7.53/2.50  tff(c_3310, plain, (![A_677, D_675]: (k3_tmap_1(A_677, '#skF_2', '#skF_1', D_675, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_675)) | ~m1_pre_topc(D_675, '#skF_1') | ~m1_pre_topc(D_675, A_677) | ~m1_pre_topc('#skF_1', A_677) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677) | v2_struct_0(A_677))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_3307])).
% 7.53/2.50  tff(c_3312, plain, (![A_678, D_679]: (k3_tmap_1(A_678, '#skF_2', '#skF_1', D_679, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_679)) | ~m1_pre_topc(D_679, '#skF_1') | ~m1_pre_topc(D_679, A_678) | ~m1_pre_topc('#skF_1', A_678) | ~l1_pre_topc(A_678) | ~v2_pre_topc(A_678) | v2_struct_0(A_678))), inference(negUnitSimplification, [status(thm)], [c_58, c_3310])).
% 7.53/2.50  tff(c_3318, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_3312])).
% 7.53/2.50  tff(c_3328, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_3288, c_44, c_3318])).
% 7.53/2.50  tff(c_3329, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_3328])).
% 7.53/2.50  tff(c_3289, plain, (![A_668, B_669, C_670, D_671]: (k2_partfun1(u1_struct_0(A_668), u1_struct_0(B_669), C_670, u1_struct_0(D_671))=k2_tmap_1(A_668, B_669, C_670, D_671) | ~m1_pre_topc(D_671, A_668) | ~m1_subset_1(C_670, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_668), u1_struct_0(B_669)))) | ~v1_funct_2(C_670, u1_struct_0(A_668), u1_struct_0(B_669)) | ~v1_funct_1(C_670) | ~l1_pre_topc(B_669) | ~v2_pre_topc(B_669) | v2_struct_0(B_669) | ~l1_pre_topc(A_668) | ~v2_pre_topc(A_668) | v2_struct_0(A_668))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.53/2.50  tff(c_3291, plain, (![D_671]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_671))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_671) | ~m1_pre_topc(D_671, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_3289])).
% 7.53/2.50  tff(c_3294, plain, (![D_671]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_671))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_671) | ~m1_pre_topc(D_671, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_3291])).
% 7.53/2.50  tff(c_3295, plain, (![D_671]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_671))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_671) | ~m1_pre_topc(D_671, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_3294])).
% 7.53/2.50  tff(c_3379, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3329, c_3295])).
% 7.53/2.50  tff(c_3386, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3379])).
% 7.53/2.50  tff(c_3448, plain, (![D_687, C_688, A_685, B_689, E_686]: (v1_funct_1(k3_tmap_1(A_685, B_689, k1_tsep_1(A_685, C_688, D_687), C_688, E_686)) | ~v5_pre_topc(E_686, k1_tsep_1(A_685, C_688, D_687), B_689) | ~m1_subset_1(E_686, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_685, C_688, D_687)), u1_struct_0(B_689)))) | ~v1_funct_2(E_686, u1_struct_0(k1_tsep_1(A_685, C_688, D_687)), u1_struct_0(B_689)) | ~v1_funct_1(E_686) | ~r4_tsep_1(A_685, C_688, D_687) | ~m1_pre_topc(D_687, A_685) | v2_struct_0(D_687) | ~m1_pre_topc(C_688, A_685) | v2_struct_0(C_688) | ~l1_pre_topc(B_689) | ~v2_pre_topc(B_689) | v2_struct_0(B_689) | ~l1_pre_topc(A_685) | ~v2_pre_topc(A_685) | v2_struct_0(A_685))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.53/2.50  tff(c_3450, plain, (![B_689, E_686]: (v1_funct_1(k3_tmap_1('#skF_1', B_689, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_686)) | ~v5_pre_topc(E_686, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_689) | ~m1_subset_1(E_686, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_689)))) | ~v1_funct_2(E_686, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_689)) | ~v1_funct_1(E_686) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_689) | ~v2_pre_topc(B_689) | v2_struct_0(B_689) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3448])).
% 7.53/2.50  tff(c_3452, plain, (![B_689, E_686]: (v1_funct_1(k3_tmap_1('#skF_1', B_689, '#skF_1', '#skF_4', E_686)) | ~v5_pre_topc(E_686, '#skF_1', B_689) | ~m1_subset_1(E_686, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_689)))) | ~v1_funct_2(E_686, u1_struct_0('#skF_1'), u1_struct_0(B_689)) | ~v1_funct_1(E_686) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_689) | ~v2_pre_topc(B_689) | v2_struct_0(B_689) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_40, c_36, c_38, c_38, c_38, c_3450])).
% 7.53/2.50  tff(c_3462, plain, (![B_692, E_693]: (v1_funct_1(k3_tmap_1('#skF_1', B_692, '#skF_1', '#skF_4', E_693)) | ~v5_pre_topc(E_693, '#skF_1', B_692) | ~m1_subset_1(E_693, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_692)))) | ~v1_funct_2(E_693, u1_struct_0('#skF_1'), u1_struct_0(B_692)) | ~v1_funct_1(E_693) | ~l1_pre_topc(B_692) | ~v2_pre_topc(B_692) | v2_struct_0(B_692))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_3452])).
% 7.53/2.50  tff(c_3465, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_3462])).
% 7.53/2.50  tff(c_3468, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_3260, c_3386, c_3465])).
% 7.53/2.50  tff(c_3470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_3261, c_3468])).
% 7.53/2.50  tff(c_3472, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_110])).
% 7.53/2.50  tff(c_3471, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_110])).
% 7.53/2.50  tff(c_3494, plain, (![A_700, B_701, C_702]: (m1_pre_topc(k1_tsep_1(A_700, B_701, C_702), A_700) | ~m1_pre_topc(C_702, A_700) | v2_struct_0(C_702) | ~m1_pre_topc(B_701, A_700) | v2_struct_0(B_701) | ~l1_pre_topc(A_700) | v2_struct_0(A_700))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.53/2.50  tff(c_3497, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_3494])).
% 7.53/2.50  tff(c_3499, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44, c_40, c_3497])).
% 7.53/2.50  tff(c_3500, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_3499])).
% 7.53/2.50  tff(c_3517, plain, (![A_712, D_710, C_711, E_709, B_708]: (k3_tmap_1(A_712, B_708, C_711, D_710, E_709)=k2_partfun1(u1_struct_0(C_711), u1_struct_0(B_708), E_709, u1_struct_0(D_710)) | ~m1_pre_topc(D_710, C_711) | ~m1_subset_1(E_709, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_711), u1_struct_0(B_708)))) | ~v1_funct_2(E_709, u1_struct_0(C_711), u1_struct_0(B_708)) | ~v1_funct_1(E_709) | ~m1_pre_topc(D_710, A_712) | ~m1_pre_topc(C_711, A_712) | ~l1_pre_topc(B_708) | ~v2_pre_topc(B_708) | v2_struct_0(B_708) | ~l1_pre_topc(A_712) | ~v2_pre_topc(A_712) | v2_struct_0(A_712))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.53/2.50  tff(c_3519, plain, (![A_712, D_710]: (k3_tmap_1(A_712, '#skF_2', '#skF_1', D_710, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_710)) | ~m1_pre_topc(D_710, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_710, A_712) | ~m1_pre_topc('#skF_1', A_712) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_712) | ~v2_pre_topc(A_712) | v2_struct_0(A_712))), inference(resolution, [status(thm)], [c_48, c_3517])).
% 7.53/2.50  tff(c_3522, plain, (![A_712, D_710]: (k3_tmap_1(A_712, '#skF_2', '#skF_1', D_710, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_710)) | ~m1_pre_topc(D_710, '#skF_1') | ~m1_pre_topc(D_710, A_712) | ~m1_pre_topc('#skF_1', A_712) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_712) | ~v2_pre_topc(A_712) | v2_struct_0(A_712))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_3519])).
% 7.53/2.50  tff(c_3530, plain, (![A_718, D_719]: (k3_tmap_1(A_718, '#skF_2', '#skF_1', D_719, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_719)) | ~m1_pre_topc(D_719, '#skF_1') | ~m1_pre_topc(D_719, A_718) | ~m1_pre_topc('#skF_1', A_718) | ~l1_pre_topc(A_718) | ~v2_pre_topc(A_718) | v2_struct_0(A_718))), inference(negUnitSimplification, [status(thm)], [c_58, c_3522])).
% 7.53/2.50  tff(c_3538, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_3530])).
% 7.53/2.50  tff(c_3550, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_3500, c_40, c_3538])).
% 7.53/2.50  tff(c_3551, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_3550])).
% 7.53/2.50  tff(c_3501, plain, (![A_703, B_704, C_705, D_706]: (k2_partfun1(u1_struct_0(A_703), u1_struct_0(B_704), C_705, u1_struct_0(D_706))=k2_tmap_1(A_703, B_704, C_705, D_706) | ~m1_pre_topc(D_706, A_703) | ~m1_subset_1(C_705, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_703), u1_struct_0(B_704)))) | ~v1_funct_2(C_705, u1_struct_0(A_703), u1_struct_0(B_704)) | ~v1_funct_1(C_705) | ~l1_pre_topc(B_704) | ~v2_pre_topc(B_704) | v2_struct_0(B_704) | ~l1_pre_topc(A_703) | ~v2_pre_topc(A_703) | v2_struct_0(A_703))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.53/2.50  tff(c_3503, plain, (![D_706]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_706))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_706) | ~m1_pre_topc(D_706, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_3501])).
% 7.53/2.50  tff(c_3506, plain, (![D_706]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_706))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_706) | ~m1_pre_topc(D_706, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_3503])).
% 7.53/2.50  tff(c_3507, plain, (![D_706]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_706))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_706) | ~m1_pre_topc(D_706, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_3506])).
% 7.53/2.50  tff(c_3633, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3551, c_3507])).
% 7.53/2.50  tff(c_3640, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3633])).
% 7.53/2.50  tff(c_3624, plain, (![B_724, C_723, D_722, E_721, A_720]: (v1_funct_1(k3_tmap_1(A_720, B_724, k1_tsep_1(A_720, C_723, D_722), D_722, E_721)) | ~v5_pre_topc(E_721, k1_tsep_1(A_720, C_723, D_722), B_724) | ~m1_subset_1(E_721, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_720, C_723, D_722)), u1_struct_0(B_724)))) | ~v1_funct_2(E_721, u1_struct_0(k1_tsep_1(A_720, C_723, D_722)), u1_struct_0(B_724)) | ~v1_funct_1(E_721) | ~r4_tsep_1(A_720, C_723, D_722) | ~m1_pre_topc(D_722, A_720) | v2_struct_0(D_722) | ~m1_pre_topc(C_723, A_720) | v2_struct_0(C_723) | ~l1_pre_topc(B_724) | ~v2_pre_topc(B_724) | v2_struct_0(B_724) | ~l1_pre_topc(A_720) | ~v2_pre_topc(A_720) | v2_struct_0(A_720))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.53/2.50  tff(c_3626, plain, (![B_724, E_721]: (v1_funct_1(k3_tmap_1('#skF_1', B_724, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_721)) | ~v5_pre_topc(E_721, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_724) | ~m1_subset_1(E_721, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_724)))) | ~v1_funct_2(E_721, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_724)) | ~v1_funct_1(E_721) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_724) | ~v2_pre_topc(B_724) | v2_struct_0(B_724) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3624])).
% 7.53/2.50  tff(c_3628, plain, (![B_724, E_721]: (v1_funct_1(k3_tmap_1('#skF_1', B_724, '#skF_1', '#skF_5', E_721)) | ~v5_pre_topc(E_721, '#skF_1', B_724) | ~m1_subset_1(E_721, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_724)))) | ~v1_funct_2(E_721, u1_struct_0('#skF_1'), u1_struct_0(B_724)) | ~v1_funct_1(E_721) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_724) | ~v2_pre_topc(B_724) | v2_struct_0(B_724) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_40, c_36, c_38, c_38, c_38, c_3626])).
% 7.53/2.50  tff(c_3674, plain, (![B_727, E_728]: (v1_funct_1(k3_tmap_1('#skF_1', B_727, '#skF_1', '#skF_5', E_728)) | ~v5_pre_topc(E_728, '#skF_1', B_727) | ~m1_subset_1(E_728, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_727)))) | ~v1_funct_2(E_728, u1_struct_0('#skF_1'), u1_struct_0(B_727)) | ~v1_funct_1(E_728) | ~l1_pre_topc(B_727) | ~v2_pre_topc(B_727) | v2_struct_0(B_727))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_3628])).
% 7.53/2.50  tff(c_3677, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_3674])).
% 7.53/2.50  tff(c_3680, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_3471, c_3640, c_3677])).
% 7.53/2.50  tff(c_3682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_3472, c_3680])).
% 7.53/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.53/2.50  
% 7.53/2.50  Inference rules
% 7.53/2.50  ----------------------
% 7.53/2.50  #Ref     : 0
% 7.53/2.50  #Sup     : 726
% 7.53/2.50  #Fact    : 0
% 7.53/2.50  #Define  : 0
% 7.53/2.50  #Split   : 12
% 7.53/2.50  #Chain   : 0
% 7.53/2.50  #Close   : 0
% 7.53/2.50  
% 7.53/2.50  Ordering : KBO
% 7.53/2.50  
% 7.53/2.50  Simplification rules
% 7.53/2.50  ----------------------
% 7.53/2.50  #Subsume      : 74
% 7.53/2.50  #Demod        : 1513
% 7.53/2.50  #Tautology    : 444
% 7.53/2.50  #SimpNegUnit  : 262
% 7.53/2.50  #BackRed      : 27
% 7.53/2.50  
% 7.53/2.50  #Partial instantiations: 0
% 7.53/2.50  #Strategies tried      : 1
% 7.53/2.50  
% 7.53/2.50  Timing (in seconds)
% 7.53/2.50  ----------------------
% 7.53/2.50  Preprocessing        : 0.43
% 7.53/2.50  Parsing              : 0.21
% 7.53/2.50  CNF conversion       : 0.06
% 7.53/2.50  Main loop            : 1.23
% 7.53/2.50  Inferencing          : 0.44
% 7.53/2.50  Reduction            : 0.38
% 7.53/2.50  Demodulation         : 0.28
% 7.53/2.51  BG Simplification    : 0.06
% 7.53/2.51  Subsumption          : 0.28
% 7.53/2.51  Abstraction          : 0.07
% 7.53/2.51  MUC search           : 0.00
% 7.53/2.51  Cooper               : 0.00
% 7.53/2.51  Total                : 1.76
% 7.53/2.51  Index Insertion      : 0.00
% 7.53/2.51  Index Deletion       : 0.00
% 7.53/2.51  Index Matching       : 0.00
% 7.53/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
