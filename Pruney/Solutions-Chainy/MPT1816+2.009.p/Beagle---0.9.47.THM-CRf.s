%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:08 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :  275 (3471 expanded)
%              Number of leaves         :   37 (1335 expanded)
%              Depth                    :   21
%              Number of atoms          :  910 (39222 expanded)
%              Number of equality atoms :   31 (1847 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_331,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_129,axiom,(
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

tff(f_162,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & v5_pre_topc(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tmap_1)).

tff(f_226,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_111,axiom,(
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

tff(f_79,axiom,(
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

tff(f_256,axiom,(
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
                    & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                 => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_41,axiom,(
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

tff(f_222,axiom,(
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
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ( ( v1_funct_1(k2_tmap_1(A,B,E,k1_tsep_1(A,C,D)))
                            & v1_funct_2(k2_tmap_1(A,B,E,k1_tsep_1(A,C,D)),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,E,k1_tsep_1(A,C,D)),k1_tsep_1(A,C,D),B)
                            & m1_subset_1(k2_tmap_1(A,B,E,k1_tsep_1(A,C,D)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k2_tmap_1(A,B,E,C))
                            & v1_funct_2(k2_tmap_1(A,B,E,C),u1_struct_0(C),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,E,C),C,B)
                            & m1_subset_1(k2_tmap_1(A,B,E,C),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
                            & v1_funct_1(k2_tmap_1(A,B,E,D))
                            & v1_funct_2(k2_tmap_1(A,B,E,D),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,E,D),D,B)
                            & m1_subset_1(k2_tmap_1(A,B,E,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).

tff(c_80,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_211,plain,(
    ! [B_145,A_146] :
      ( l1_pre_topc(B_145)
      | ~ m1_pre_topc(B_145,A_146)
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_217,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_211])).

tff(c_224,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_217])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_70,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_3345,plain,(
    ! [A_605,B_606,C_607,D_608] :
      ( v1_funct_1(k2_tmap_1(A_605,B_606,C_607,D_608))
      | ~ l1_struct_0(D_608)
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_605),u1_struct_0(B_606))))
      | ~ v1_funct_2(C_607,u1_struct_0(A_605),u1_struct_0(B_606))
      | ~ v1_funct_1(C_607)
      | ~ l1_struct_0(B_606)
      | ~ l1_struct_0(A_605) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3347,plain,(
    ! [D_608] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_608))
      | ~ l1_struct_0(D_608)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_3345])).

tff(c_3350,plain,(
    ! [D_608] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_608))
      | ~ l1_struct_0(D_608)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_3347])).

tff(c_3351,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3350])).

tff(c_3361,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_3351])).

tff(c_3365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3361])).

tff(c_3366,plain,(
    ! [D_608] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_608))
      | ~ l1_struct_0(D_608) ) ),
    inference(splitRight,[status(thm)],[c_3350])).

tff(c_3368,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3366])).

tff(c_3373,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_3368])).

tff(c_3377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3373])).

tff(c_3380,plain,(
    ! [D_613] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_613))
      | ~ l1_struct_0(D_613) ) ),
    inference(splitRight,[status(thm)],[c_3366])).

tff(c_60,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_220,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_211])).

tff(c_227,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_220])).

tff(c_3239,plain,(
    ! [A_586,B_587,C_588,D_589] :
      ( v1_funct_1(k2_tmap_1(A_586,B_587,C_588,D_589))
      | ~ l1_struct_0(D_589)
      | ~ m1_subset_1(C_588,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_586),u1_struct_0(B_587))))
      | ~ v1_funct_2(C_588,u1_struct_0(A_586),u1_struct_0(B_587))
      | ~ v1_funct_1(C_588)
      | ~ l1_struct_0(B_587)
      | ~ l1_struct_0(A_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3241,plain,(
    ! [D_589] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_589))
      | ~ l1_struct_0(D_589)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_3239])).

tff(c_3244,plain,(
    ! [D_589] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_589))
      | ~ l1_struct_0(D_589)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_3241])).

tff(c_3245,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3244])).

tff(c_3248,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_3245])).

tff(c_3252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3248])).

tff(c_3253,plain,(
    ! [D_589] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_589))
      | ~ l1_struct_0(D_589) ) ),
    inference(splitRight,[status(thm)],[c_3244])).

tff(c_3255,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3253])).

tff(c_3258,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_3255])).

tff(c_3262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3258])).

tff(c_3272,plain,(
    ! [D_594] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_594))
      | ~ l1_struct_0(D_594) ) ),
    inference(splitRight,[status(thm)],[c_3253])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_82,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_2773,plain,(
    ! [A_469,B_470,C_471,D_472] :
      ( v1_funct_1(k2_tmap_1(A_469,B_470,C_471,D_472))
      | ~ l1_struct_0(D_472)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_469),u1_struct_0(B_470))))
      | ~ v1_funct_2(C_471,u1_struct_0(A_469),u1_struct_0(B_470))
      | ~ v1_funct_1(C_471)
      | ~ l1_struct_0(B_470)
      | ~ l1_struct_0(A_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2775,plain,(
    ! [D_472] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_472))
      | ~ l1_struct_0(D_472)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_2773])).

tff(c_2778,plain,(
    ! [D_472] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_472))
      | ~ l1_struct_0(D_472)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2775])).

tff(c_2779,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2778])).

tff(c_2782,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_2779])).

tff(c_2786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2782])).

tff(c_2788,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2778])).

tff(c_2787,plain,(
    ! [D_472] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_472))
      | ~ l1_struct_0(D_472) ) ),
    inference(splitRight,[status(thm)],[c_2778])).

tff(c_2808,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2787])).

tff(c_2811,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2808])).

tff(c_2815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2811])).

tff(c_2817,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2787])).

tff(c_2826,plain,(
    ! [A_480,B_481,C_482,D_483] :
      ( v1_funct_2(k2_tmap_1(A_480,B_481,C_482,D_483),u1_struct_0(D_483),u1_struct_0(B_481))
      | ~ l1_struct_0(D_483)
      | ~ m1_subset_1(C_482,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_480),u1_struct_0(B_481))))
      | ~ v1_funct_2(C_482,u1_struct_0(A_480),u1_struct_0(B_481))
      | ~ v1_funct_1(C_482)
      | ~ l1_struct_0(B_481)
      | ~ l1_struct_0(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2828,plain,(
    ! [D_483] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_483),u1_struct_0(D_483),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_483)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_2826])).

tff(c_2832,plain,(
    ! [D_484] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_484),u1_struct_0(D_484),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_484) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2788,c_2817,c_72,c_70,c_2828])).

tff(c_2683,plain,(
    ! [A_446,B_447,C_448,D_449] :
      ( v1_funct_1(k2_tmap_1(A_446,B_447,C_448,D_449))
      | ~ l1_struct_0(D_449)
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_446),u1_struct_0(B_447))))
      | ~ v1_funct_2(C_448,u1_struct_0(A_446),u1_struct_0(B_447))
      | ~ v1_funct_1(C_448)
      | ~ l1_struct_0(B_447)
      | ~ l1_struct_0(A_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2685,plain,(
    ! [D_449] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_449))
      | ~ l1_struct_0(D_449)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_2683])).

tff(c_2688,plain,(
    ! [D_449] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_449))
      | ~ l1_struct_0(D_449)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2685])).

tff(c_2696,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2688])).

tff(c_2699,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_2696])).

tff(c_2703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2699])).

tff(c_2705,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2688])).

tff(c_2704,plain,(
    ! [D_449] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_449))
      | ~ l1_struct_0(D_449) ) ),
    inference(splitRight,[status(thm)],[c_2688])).

tff(c_2706,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2704])).

tff(c_2709,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2706])).

tff(c_2713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2709])).

tff(c_2715,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2704])).

tff(c_2717,plain,(
    ! [A_455,B_456,C_457,D_458] :
      ( v1_funct_2(k2_tmap_1(A_455,B_456,C_457,D_458),u1_struct_0(D_458),u1_struct_0(B_456))
      | ~ l1_struct_0(D_458)
      | ~ m1_subset_1(C_457,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_455),u1_struct_0(B_456))))
      | ~ v1_funct_2(C_457,u1_struct_0(A_455),u1_struct_0(B_456))
      | ~ v1_funct_1(C_457)
      | ~ l1_struct_0(B_456)
      | ~ l1_struct_0(A_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2719,plain,(
    ! [D_458] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_458),u1_struct_0(D_458),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_458)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_2717])).

tff(c_2723,plain,(
    ! [D_459] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_459),u1_struct_0(D_459),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_459) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2705,c_2715,c_72,c_70,c_2719])).

tff(c_2582,plain,(
    ! [A_420,B_421,C_422,D_423] :
      ( v1_funct_1(k2_tmap_1(A_420,B_421,C_422,D_423))
      | ~ l1_struct_0(D_423)
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_420),u1_struct_0(B_421))))
      | ~ v1_funct_2(C_422,u1_struct_0(A_420),u1_struct_0(B_421))
      | ~ v1_funct_1(C_422)
      | ~ l1_struct_0(B_421)
      | ~ l1_struct_0(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2584,plain,(
    ! [D_423] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_423))
      | ~ l1_struct_0(D_423)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_2582])).

tff(c_2587,plain,(
    ! [D_423] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_423))
      | ~ l1_struct_0(D_423)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2584])).

tff(c_2588,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2587])).

tff(c_2598,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_2588])).

tff(c_2602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2598])).

tff(c_2604,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2587])).

tff(c_2603,plain,(
    ! [D_423] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_423))
      | ~ l1_struct_0(D_423) ) ),
    inference(splitRight,[status(thm)],[c_2587])).

tff(c_2605,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2603])).

tff(c_2610,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2605])).

tff(c_2614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2610])).

tff(c_2616,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2603])).

tff(c_2631,plain,(
    ! [A_437,B_438,C_439,D_440] :
      ( m1_subset_1(k2_tmap_1(A_437,B_438,C_439,D_440),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_440),u1_struct_0(B_438))))
      | ~ l1_struct_0(D_440)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_437),u1_struct_0(B_438))))
      | ~ v1_funct_2(C_439,u1_struct_0(A_437),u1_struct_0(B_438))
      | ~ v1_funct_1(C_439)
      | ~ l1_struct_0(B_438)
      | ~ l1_struct_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2410,plain,(
    ! [A_385,B_386,C_387,D_388] :
      ( v1_funct_1(k2_tmap_1(A_385,B_386,C_387,D_388))
      | ~ l1_struct_0(D_388)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385),u1_struct_0(B_386))))
      | ~ v1_funct_2(C_387,u1_struct_0(A_385),u1_struct_0(B_386))
      | ~ v1_funct_1(C_387)
      | ~ l1_struct_0(B_386)
      | ~ l1_struct_0(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2414,plain,(
    ! [D_388] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_388))
      | ~ l1_struct_0(D_388)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_2410])).

tff(c_2420,plain,(
    ! [D_388] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_388))
      | ~ l1_struct_0(D_388)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2414])).

tff(c_2421,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2420])).

tff(c_2424,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_2421])).

tff(c_2428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2424])).

tff(c_2430,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2420])).

tff(c_2429,plain,(
    ! [D_388] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_388))
      | ~ l1_struct_0(D_388) ) ),
    inference(splitRight,[status(thm)],[c_2420])).

tff(c_2450,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2429])).

tff(c_2453,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2450])).

tff(c_2457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2453])).

tff(c_2459,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2429])).

tff(c_2515,plain,(
    ! [A_407,B_408,C_409,D_410] :
      ( m1_subset_1(k2_tmap_1(A_407,B_408,C_409,D_410),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_410),u1_struct_0(B_408))))
      | ~ l1_struct_0(D_410)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_407),u1_struct_0(B_408))))
      | ~ v1_funct_2(C_409,u1_struct_0(A_407),u1_struct_0(B_408))
      | ~ v1_funct_1(C_409)
      | ~ l1_struct_0(B_408)
      | ~ l1_struct_0(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_413,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( v1_funct_1(k2_tmap_1(A_179,B_180,C_181,D_182))
      | ~ m1_pre_topc(D_182,A_179)
      | v2_struct_0(D_182)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_179),u1_struct_0(B_180))))
      | ~ v5_pre_topc(C_181,A_179,B_180)
      | ~ v1_funct_2(C_181,u1_struct_0(A_179),u1_struct_0(B_180))
      | ~ v1_funct_1(C_181)
      | ~ l1_pre_topc(B_180)
      | ~ v2_pre_topc(B_180)
      | v2_struct_0(B_180)
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_421,plain,(
    ! [D_182] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_182))
      | ~ m1_pre_topc(D_182,'#skF_1')
      | v2_struct_0(D_182)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_413])).

tff(c_433,plain,(
    ! [D_182] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_182))
      | ~ m1_pre_topc(D_182,'#skF_1')
      | v2_struct_0(D_182)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_72,c_70,c_421])).

tff(c_434,plain,(
    ! [D_182] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_182))
      | ~ m1_pre_topc(D_182,'#skF_1')
      | v2_struct_0(D_182)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_433])).

tff(c_435,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_434])).

tff(c_56,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_170,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_228,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_160,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_242,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_150,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_230,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_58,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_298,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( v1_funct_1(k2_tmap_1(A_157,B_158,C_159,D_160))
      | ~ l1_struct_0(D_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_157),u1_struct_0(B_158))))
      | ~ v1_funct_2(C_159,u1_struct_0(A_157),u1_struct_0(B_158))
      | ~ v1_funct_1(C_159)
      | ~ l1_struct_0(B_158)
      | ~ l1_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_304,plain,(
    ! [D_160] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_160))
      | ~ l1_struct_0(D_160)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_298])).

tff(c_313,plain,(
    ! [D_160] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_160))
      | ~ l1_struct_0(D_160)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_304])).

tff(c_333,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_336,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_333])).

tff(c_340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_336])).

tff(c_342,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_341,plain,(
    ! [D_160] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_160))
      | ~ l1_struct_0(D_160) ) ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_343,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_346,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_343])).

tff(c_350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_346])).

tff(c_352,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_366,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( v1_funct_2(k2_tmap_1(A_166,B_167,C_168,D_169),u1_struct_0(D_169),u1_struct_0(B_167))
      | ~ l1_struct_0(D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166),u1_struct_0(B_167))))
      | ~ v1_funct_2(C_168,u1_struct_0(A_166),u1_struct_0(B_167))
      | ~ v1_funct_1(C_168)
      | ~ l1_struct_0(B_167)
      | ~ l1_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_372,plain,(
    ! [D_169] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_169),u1_struct_0(D_169),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_169)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_366])).

tff(c_381,plain,(
    ! [D_169] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_169),u1_struct_0(D_169),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_352,c_72,c_70,c_372])).

tff(c_14,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( m1_subset_1(k2_tmap_1(A_55,B_56,C_57,D_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_58),u1_struct_0(B_56))))
      | ~ l1_struct_0(D_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_55),u1_struct_0(B_56))))
      | ~ v1_funct_2(C_57,u1_struct_0(A_55),u1_struct_0(B_56))
      | ~ v1_funct_1(C_57)
      | ~ l1_struct_0(B_56)
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_351,plain,(
    ! [D_160] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_160))
      | ~ l1_struct_0(D_160) ) ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_50,plain,(
    ! [A_94] :
      ( m1_pre_topc(A_94,A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_582,plain,(
    ! [D_217,C_216,B_214,A_215,E_213] :
      ( k3_tmap_1(A_215,B_214,C_216,D_217,E_213) = k2_partfun1(u1_struct_0(C_216),u1_struct_0(B_214),E_213,u1_struct_0(D_217))
      | ~ m1_pre_topc(D_217,C_216)
      | ~ m1_subset_1(E_213,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_216),u1_struct_0(B_214))))
      | ~ v1_funct_2(E_213,u1_struct_0(C_216),u1_struct_0(B_214))
      | ~ v1_funct_1(E_213)
      | ~ m1_pre_topc(D_217,A_215)
      | ~ m1_pre_topc(C_216,A_215)
      | ~ l1_pre_topc(B_214)
      | ~ v2_pre_topc(B_214)
      | v2_struct_0(B_214)
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_590,plain,(
    ! [A_215,D_217] :
      ( k3_tmap_1(A_215,'#skF_2','#skF_1',D_217,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_217))
      | ~ m1_pre_topc(D_217,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_217,A_215)
      | ~ m1_pre_topc('#skF_1',A_215)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_68,c_582])).

tff(c_602,plain,(
    ! [A_215,D_217] :
      ( k3_tmap_1(A_215,'#skF_2','#skF_1',D_217,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_217))
      | ~ m1_pre_topc(D_217,'#skF_1')
      | ~ m1_pre_topc(D_217,A_215)
      | ~ m1_pre_topc('#skF_1',A_215)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_590])).

tff(c_605,plain,(
    ! [A_220,D_221] :
      ( k3_tmap_1(A_220,'#skF_2','#skF_1',D_221,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_221))
      | ~ m1_pre_topc(D_221,'#skF_1')
      | ~ m1_pre_topc(D_221,A_220)
      | ~ m1_pre_topc('#skF_1',A_220)
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_602])).

tff(c_611,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_605])).

tff(c_620,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_64,c_611])).

tff(c_621,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_620])).

tff(c_626,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_621])).

tff(c_630,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_626])).

tff(c_634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_630])).

tff(c_636,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_603,plain,(
    ! [A_215,D_217] :
      ( k3_tmap_1(A_215,'#skF_2','#skF_1',D_217,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_217))
      | ~ m1_pre_topc(D_217,'#skF_1')
      | ~ m1_pre_topc(D_217,A_215)
      | ~ m1_pre_topc('#skF_1',A_215)
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_602])).

tff(c_638,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_636,c_603])).

tff(c_651,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_636,c_638])).

tff(c_652,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_651])).

tff(c_438,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( k2_partfun1(u1_struct_0(A_183),u1_struct_0(B_184),C_185,u1_struct_0(D_186)) = k2_tmap_1(A_183,B_184,C_185,D_186)
      | ~ m1_pre_topc(D_186,A_183)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183),u1_struct_0(B_184))))
      | ~ v1_funct_2(C_185,u1_struct_0(A_183),u1_struct_0(B_184))
      | ~ v1_funct_1(C_185)
      | ~ l1_pre_topc(B_184)
      | ~ v2_pre_topc(B_184)
      | v2_struct_0(B_184)
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_446,plain,(
    ! [D_186] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_186)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_186)
      | ~ m1_pre_topc(D_186,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_438])).

tff(c_458,plain,(
    ! [D_186] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_186)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_186)
      | ~ m1_pre_topc(D_186,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_72,c_70,c_446])).

tff(c_459,plain,(
    ! [D_186] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_186)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_186)
      | ~ m1_pre_topc(D_186,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_458])).

tff(c_704,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_459])).

tff(c_711,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_704])).

tff(c_469,plain,(
    ! [C_188,B_189,D_190,A_191] :
      ( r2_funct_2(u1_struct_0(C_188),u1_struct_0(B_189),D_190,k3_tmap_1(A_191,B_189,C_188,C_188,D_190))
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_188),u1_struct_0(B_189))))
      | ~ v1_funct_2(D_190,u1_struct_0(C_188),u1_struct_0(B_189))
      | ~ v1_funct_1(D_190)
      | ~ m1_pre_topc(C_188,A_191)
      | v2_struct_0(C_188)
      | ~ l1_pre_topc(B_189)
      | ~ v2_pre_topc(B_189)
      | v2_struct_0(B_189)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_477,plain,(
    ! [A_191] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_191,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_1',A_191)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_68,c_469])).

tff(c_489,plain,(
    ! [A_191] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_191,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_191)
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_477])).

tff(c_491,plain,(
    ! [A_192] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_192,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_84,c_489])).

tff(c_4,plain,(
    ! [D_4,C_3,A_1,B_2] :
      ( D_4 = C_3
      | ~ r2_funct_2(A_1,B_2,C_3,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_493,plain,(
    ! [A_192] :
      ( k3_tmap_1(A_192,'#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
      | ~ m1_subset_1(k3_tmap_1(A_192,'#skF_2','#skF_1','#skF_1','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_192,'#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_192,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_1',A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(resolution,[status(thm)],[c_491,c_4])).

tff(c_496,plain,(
    ! [A_192] :
      ( k3_tmap_1(A_192,'#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
      | ~ m1_subset_1(k3_tmap_1(A_192,'#skF_2','#skF_1','#skF_1','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_192,'#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_192,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_493])).

tff(c_719,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_496])).

tff(c_726,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_636,c_711,c_711,c_711,c_719])).

tff(c_727,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_726])).

tff(c_886,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_727])).

tff(c_889,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_351,c_886])).

tff(c_893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_889])).

tff(c_894,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_727])).

tff(c_929,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_894])).

tff(c_950,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_929])).

tff(c_954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_352,c_72,c_70,c_68,c_950])).

tff(c_955,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_894])).

tff(c_1008,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_955])).

tff(c_1012,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_381,c_1008])).

tff(c_1016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_1012])).

tff(c_1017,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_955])).

tff(c_140,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_261,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_130,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_229,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_120,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_260,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_110,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_231,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_100,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_262,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_2220,plain,(
    ! [E_371,A_368,B_369,D_367,C_370] :
      ( v5_pre_topc(k2_tmap_1(A_368,B_369,E_371,k1_tsep_1(A_368,C_370,D_367)),k1_tsep_1(A_368,C_370,D_367),B_369)
      | ~ m1_subset_1(k2_tmap_1(A_368,B_369,E_371,D_367),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_367),u1_struct_0(B_369))))
      | ~ v5_pre_topc(k2_tmap_1(A_368,B_369,E_371,D_367),D_367,B_369)
      | ~ v1_funct_2(k2_tmap_1(A_368,B_369,E_371,D_367),u1_struct_0(D_367),u1_struct_0(B_369))
      | ~ v1_funct_1(k2_tmap_1(A_368,B_369,E_371,D_367))
      | ~ m1_subset_1(k2_tmap_1(A_368,B_369,E_371,C_370),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_370),u1_struct_0(B_369))))
      | ~ v5_pre_topc(k2_tmap_1(A_368,B_369,E_371,C_370),C_370,B_369)
      | ~ v1_funct_2(k2_tmap_1(A_368,B_369,E_371,C_370),u1_struct_0(C_370),u1_struct_0(B_369))
      | ~ v1_funct_1(k2_tmap_1(A_368,B_369,E_371,C_370))
      | ~ m1_subset_1(E_371,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_368),u1_struct_0(B_369))))
      | ~ v1_funct_2(E_371,u1_struct_0(A_368),u1_struct_0(B_369))
      | ~ v1_funct_1(E_371)
      | ~ r4_tsep_1(A_368,C_370,D_367)
      | ~ m1_pre_topc(D_367,A_368)
      | v2_struct_0(D_367)
      | ~ m1_pre_topc(C_370,A_368)
      | v2_struct_0(C_370)
      | ~ l1_pre_topc(B_369)
      | ~ v2_pre_topc(B_369)
      | v2_struct_0(B_369)
      | ~ l1_pre_topc(A_368)
      | ~ v2_pre_topc(A_368)
      | v2_struct_0(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_2230,plain,(
    ! [C_370] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_370,'#skF_5')),k1_tsep_1('#skF_1',C_370,'#skF_5'),'#skF_2')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_370),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_370),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_370),C_370,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_370),u1_struct_0(C_370),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_370))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ r4_tsep_1('#skF_1',C_370,'#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_370,'#skF_1')
      | v2_struct_0(C_370)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_262,c_2220])).

tff(c_2247,plain,(
    ! [C_370] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_370,'#skF_5')),k1_tsep_1('#skF_1',C_370,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_370),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_370),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_370),C_370,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_370),u1_struct_0(C_370),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_370))
      | ~ r4_tsep_1('#skF_1',C_370,'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_370,'#skF_1')
      | v2_struct_0(C_370)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_60,c_72,c_70,c_68,c_229,c_260,c_231,c_2230])).

tff(c_2314,plain,(
    ! [C_375] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_375,'#skF_5')),k1_tsep_1('#skF_1',C_375,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_375),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_375),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_375),C_375,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_375),u1_struct_0(C_375),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_375))
      | ~ r4_tsep_1('#skF_1',C_375,'#skF_5')
      | ~ m1_pre_topc(C_375,'#skF_1')
      | v2_struct_0(C_375) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_62,c_2247])).

tff(c_2335,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_261,c_2314])).

tff(c_2356,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_56,c_228,c_242,c_230,c_58,c_1017,c_58,c_2335])).

tff(c_2358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_435,c_2356])).

tff(c_2360,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_86,plain,
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
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_184,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_86])).

tff(c_194,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_184])).

tff(c_204,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_194])).

tff(c_2396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_228,c_242,c_230,c_261,c_229,c_260,c_231,c_262,c_204])).

tff(c_2398,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_2524,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2515,c_2398])).

tff(c_2530,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2430,c_2459,c_72,c_70,c_68,c_2524])).

tff(c_2549,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_2530])).

tff(c_2553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_2549])).

tff(c_2555,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_2640,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2631,c_2555])).

tff(c_2646,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2604,c_2616,c_72,c_70,c_68,c_2640])).

tff(c_2649,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2646])).

tff(c_2653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_2649])).

tff(c_2655,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_2727,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2723,c_2655])).

tff(c_2740,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_2727])).

tff(c_2744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_2740])).

tff(c_2746,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_2836,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2832,c_2746])).

tff(c_2839,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2836])).

tff(c_2843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_2839])).

tff(c_2844,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_2985,plain,(
    ! [A_523,B_524,C_525,D_526] :
      ( v5_pre_topc(k2_tmap_1(A_523,B_524,C_525,D_526),D_526,B_524)
      | ~ m1_pre_topc(D_526,A_523)
      | v2_struct_0(D_526)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_523),u1_struct_0(B_524))))
      | ~ v5_pre_topc(C_525,A_523,B_524)
      | ~ v1_funct_2(C_525,u1_struct_0(A_523),u1_struct_0(B_524))
      | ~ v1_funct_1(C_525)
      | ~ l1_pre_topc(B_524)
      | ~ v2_pre_topc(B_524)
      | v2_struct_0(B_524)
      | ~ l1_pre_topc(A_523)
      | ~ v2_pre_topc(A_523)
      | v2_struct_0(A_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2989,plain,(
    ! [D_526] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_526),D_526,'#skF_2')
      | ~ m1_pre_topc(D_526,'#skF_1')
      | v2_struct_0(D_526)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_2985])).

tff(c_2993,plain,(
    ! [D_526] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_526),D_526,'#skF_2')
      | ~ m1_pre_topc(D_526,'#skF_1')
      | v2_struct_0(D_526)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_72,c_70,c_2844,c_2989])).

tff(c_2995,plain,(
    ! [D_527] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_527),D_527,'#skF_2')
      | ~ m1_pre_topc(D_527,'#skF_1')
      | v2_struct_0(D_527) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_2993])).

tff(c_2845,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_2998,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2995,c_2845])).

tff(c_3001,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2998])).

tff(c_3003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3001])).

tff(c_3004,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_3160,plain,(
    ! [A_571,B_572,C_573,D_574] :
      ( v5_pre_topc(k2_tmap_1(A_571,B_572,C_573,D_574),D_574,B_572)
      | ~ m1_pre_topc(D_574,A_571)
      | v2_struct_0(D_574)
      | ~ m1_subset_1(C_573,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_571),u1_struct_0(B_572))))
      | ~ v5_pre_topc(C_573,A_571,B_572)
      | ~ v1_funct_2(C_573,u1_struct_0(A_571),u1_struct_0(B_572))
      | ~ v1_funct_1(C_573)
      | ~ l1_pre_topc(B_572)
      | ~ v2_pre_topc(B_572)
      | v2_struct_0(B_572)
      | ~ l1_pre_topc(A_571)
      | ~ v2_pre_topc(A_571)
      | v2_struct_0(A_571) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3164,plain,(
    ! [D_574] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_574),D_574,'#skF_2')
      | ~ m1_pre_topc(D_574,'#skF_1')
      | v2_struct_0(D_574)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_3160])).

tff(c_3168,plain,(
    ! [D_574] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_574),D_574,'#skF_2')
      | ~ m1_pre_topc(D_574,'#skF_1')
      | v2_struct_0(D_574)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_72,c_70,c_3004,c_3164])).

tff(c_3170,plain,(
    ! [D_575] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_575),D_575,'#skF_2')
      | ~ m1_pre_topc(D_575,'#skF_1')
      | v2_struct_0(D_575) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_3168])).

tff(c_3005,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_3173,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3170,c_3005])).

tff(c_3176,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3173])).

tff(c_3178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3176])).

tff(c_3180,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_3276,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3272,c_3180])).

tff(c_3279,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_3276])).

tff(c_3283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_3279])).

tff(c_3285,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_3384,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3380,c_3285])).

tff(c_3387,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_3384])).

tff(c_3391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_3387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.32/2.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.39/2.43  
% 7.39/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.39/2.43  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.39/2.43  
% 7.39/2.43  %Foreground sorts:
% 7.39/2.43  
% 7.39/2.43  
% 7.39/2.43  %Background operators:
% 7.39/2.43  
% 7.39/2.43  
% 7.39/2.43  %Foreground operators:
% 7.39/2.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.39/2.43  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 7.39/2.43  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.39/2.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.39/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.39/2.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.39/2.43  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 7.39/2.43  tff('#skF_5', type, '#skF_5': $i).
% 7.39/2.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.39/2.43  tff('#skF_2', type, '#skF_2': $i).
% 7.39/2.43  tff('#skF_3', type, '#skF_3': $i).
% 7.39/2.43  tff('#skF_1', type, '#skF_1': $i).
% 7.39/2.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.39/2.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.39/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.39/2.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.39/2.43  tff('#skF_4', type, '#skF_4': $i).
% 7.39/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.39/2.43  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.39/2.43  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.39/2.43  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.39/2.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.39/2.43  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.39/2.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.39/2.43  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.39/2.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.39/2.43  
% 7.39/2.47  tff(f_331, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (((A = k1_tsep_1(A, D, E)) & r4_tsep_1(A, D, E)) => ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, C, E))) & v1_funct_2(k2_tmap_1(A, B, C, E), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, E), E, B)) & m1_subset_1(k2_tmap_1(A, B, C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_tmap_1)).
% 7.39/2.47  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.39/2.47  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.39/2.47  tff(f_129, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 7.39/2.47  tff(f_162, axiom, (![A, B, C, D]: ((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tmap_1)).
% 7.39/2.47  tff(f_226, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.39/2.47  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 7.39/2.47  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.39/2.47  tff(f_256, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 7.39/2.47  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.39/2.47  tff(f_222, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_funct_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D))) & v1_funct_2(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_tsep_1(A, C, D), B)) & m1_subset_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, E, C)) & v1_funct_2(k2_tmap_1(A, B, E, C), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, C), C, B)) & m1_subset_1(k2_tmap_1(A, B, E, C), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, E, D))) & v1_funct_2(k2_tmap_1(A, B, E, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, E, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_tmap_1)).
% 7.39/2.47  tff(c_80, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_211, plain, (![B_145, A_146]: (l1_pre_topc(B_145) | ~m1_pre_topc(B_145, A_146) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.39/2.47  tff(c_217, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_211])).
% 7.39/2.47  tff(c_224, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_217])).
% 7.39/2.47  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.39/2.47  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_70, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_3345, plain, (![A_605, B_606, C_607, D_608]: (v1_funct_1(k2_tmap_1(A_605, B_606, C_607, D_608)) | ~l1_struct_0(D_608) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_605), u1_struct_0(B_606)))) | ~v1_funct_2(C_607, u1_struct_0(A_605), u1_struct_0(B_606)) | ~v1_funct_1(C_607) | ~l1_struct_0(B_606) | ~l1_struct_0(A_605))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_3347, plain, (![D_608]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_608)) | ~l1_struct_0(D_608) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_3345])).
% 7.39/2.47  tff(c_3350, plain, (![D_608]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_608)) | ~l1_struct_0(D_608) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_3347])).
% 7.39/2.47  tff(c_3351, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3350])).
% 7.39/2.47  tff(c_3361, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_3351])).
% 7.39/2.47  tff(c_3365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_3361])).
% 7.39/2.47  tff(c_3366, plain, (![D_608]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_608)) | ~l1_struct_0(D_608))), inference(splitRight, [status(thm)], [c_3350])).
% 7.39/2.47  tff(c_3368, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3366])).
% 7.39/2.47  tff(c_3373, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_3368])).
% 7.39/2.47  tff(c_3377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_3373])).
% 7.39/2.47  tff(c_3380, plain, (![D_613]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_613)) | ~l1_struct_0(D_613))), inference(splitRight, [status(thm)], [c_3366])).
% 7.39/2.47  tff(c_60, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_220, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_211])).
% 7.39/2.47  tff(c_227, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_220])).
% 7.39/2.47  tff(c_3239, plain, (![A_586, B_587, C_588, D_589]: (v1_funct_1(k2_tmap_1(A_586, B_587, C_588, D_589)) | ~l1_struct_0(D_589) | ~m1_subset_1(C_588, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_586), u1_struct_0(B_587)))) | ~v1_funct_2(C_588, u1_struct_0(A_586), u1_struct_0(B_587)) | ~v1_funct_1(C_588) | ~l1_struct_0(B_587) | ~l1_struct_0(A_586))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_3241, plain, (![D_589]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_589)) | ~l1_struct_0(D_589) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_3239])).
% 7.39/2.47  tff(c_3244, plain, (![D_589]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_589)) | ~l1_struct_0(D_589) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_3241])).
% 7.39/2.47  tff(c_3245, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3244])).
% 7.39/2.47  tff(c_3248, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_3245])).
% 7.39/2.47  tff(c_3252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_3248])).
% 7.39/2.47  tff(c_3253, plain, (![D_589]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_589)) | ~l1_struct_0(D_589))), inference(splitRight, [status(thm)], [c_3244])).
% 7.39/2.47  tff(c_3255, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3253])).
% 7.39/2.47  tff(c_3258, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_3255])).
% 7.39/2.47  tff(c_3262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_3258])).
% 7.39/2.47  tff(c_3272, plain, (![D_594]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_594)) | ~l1_struct_0(D_594))), inference(splitRight, [status(thm)], [c_3253])).
% 7.39/2.47  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_84, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_82, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_2773, plain, (![A_469, B_470, C_471, D_472]: (v1_funct_1(k2_tmap_1(A_469, B_470, C_471, D_472)) | ~l1_struct_0(D_472) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_469), u1_struct_0(B_470)))) | ~v1_funct_2(C_471, u1_struct_0(A_469), u1_struct_0(B_470)) | ~v1_funct_1(C_471) | ~l1_struct_0(B_470) | ~l1_struct_0(A_469))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_2775, plain, (![D_472]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_472)) | ~l1_struct_0(D_472) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_2773])).
% 7.39/2.47  tff(c_2778, plain, (![D_472]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_472)) | ~l1_struct_0(D_472) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2775])).
% 7.39/2.47  tff(c_2779, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2778])).
% 7.39/2.47  tff(c_2782, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_2779])).
% 7.39/2.47  tff(c_2786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_2782])).
% 7.39/2.47  tff(c_2788, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_2778])).
% 7.39/2.47  tff(c_2787, plain, (![D_472]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_472)) | ~l1_struct_0(D_472))), inference(splitRight, [status(thm)], [c_2778])).
% 7.39/2.47  tff(c_2808, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2787])).
% 7.39/2.47  tff(c_2811, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_2808])).
% 7.39/2.47  tff(c_2815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_2811])).
% 7.39/2.47  tff(c_2817, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_2787])).
% 7.39/2.47  tff(c_2826, plain, (![A_480, B_481, C_482, D_483]: (v1_funct_2(k2_tmap_1(A_480, B_481, C_482, D_483), u1_struct_0(D_483), u1_struct_0(B_481)) | ~l1_struct_0(D_483) | ~m1_subset_1(C_482, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_480), u1_struct_0(B_481)))) | ~v1_funct_2(C_482, u1_struct_0(A_480), u1_struct_0(B_481)) | ~v1_funct_1(C_482) | ~l1_struct_0(B_481) | ~l1_struct_0(A_480))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_2828, plain, (![D_483]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_483), u1_struct_0(D_483), u1_struct_0('#skF_2')) | ~l1_struct_0(D_483) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_2826])).
% 7.39/2.47  tff(c_2832, plain, (![D_484]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_484), u1_struct_0(D_484), u1_struct_0('#skF_2')) | ~l1_struct_0(D_484))), inference(demodulation, [status(thm), theory('equality')], [c_2788, c_2817, c_72, c_70, c_2828])).
% 7.39/2.47  tff(c_2683, plain, (![A_446, B_447, C_448, D_449]: (v1_funct_1(k2_tmap_1(A_446, B_447, C_448, D_449)) | ~l1_struct_0(D_449) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_446), u1_struct_0(B_447)))) | ~v1_funct_2(C_448, u1_struct_0(A_446), u1_struct_0(B_447)) | ~v1_funct_1(C_448) | ~l1_struct_0(B_447) | ~l1_struct_0(A_446))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_2685, plain, (![D_449]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_449)) | ~l1_struct_0(D_449) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_2683])).
% 7.39/2.47  tff(c_2688, plain, (![D_449]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_449)) | ~l1_struct_0(D_449) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2685])).
% 7.39/2.47  tff(c_2696, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2688])).
% 7.39/2.47  tff(c_2699, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_2696])).
% 7.39/2.47  tff(c_2703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_2699])).
% 7.39/2.47  tff(c_2705, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_2688])).
% 7.39/2.47  tff(c_2704, plain, (![D_449]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_449)) | ~l1_struct_0(D_449))), inference(splitRight, [status(thm)], [c_2688])).
% 7.39/2.47  tff(c_2706, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2704])).
% 7.39/2.47  tff(c_2709, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_2706])).
% 7.39/2.47  tff(c_2713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_2709])).
% 7.39/2.47  tff(c_2715, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_2704])).
% 7.39/2.47  tff(c_2717, plain, (![A_455, B_456, C_457, D_458]: (v1_funct_2(k2_tmap_1(A_455, B_456, C_457, D_458), u1_struct_0(D_458), u1_struct_0(B_456)) | ~l1_struct_0(D_458) | ~m1_subset_1(C_457, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_455), u1_struct_0(B_456)))) | ~v1_funct_2(C_457, u1_struct_0(A_455), u1_struct_0(B_456)) | ~v1_funct_1(C_457) | ~l1_struct_0(B_456) | ~l1_struct_0(A_455))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_2719, plain, (![D_458]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_458), u1_struct_0(D_458), u1_struct_0('#skF_2')) | ~l1_struct_0(D_458) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_2717])).
% 7.39/2.47  tff(c_2723, plain, (![D_459]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_459), u1_struct_0(D_459), u1_struct_0('#skF_2')) | ~l1_struct_0(D_459))), inference(demodulation, [status(thm), theory('equality')], [c_2705, c_2715, c_72, c_70, c_2719])).
% 7.39/2.47  tff(c_2582, plain, (![A_420, B_421, C_422, D_423]: (v1_funct_1(k2_tmap_1(A_420, B_421, C_422, D_423)) | ~l1_struct_0(D_423) | ~m1_subset_1(C_422, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_420), u1_struct_0(B_421)))) | ~v1_funct_2(C_422, u1_struct_0(A_420), u1_struct_0(B_421)) | ~v1_funct_1(C_422) | ~l1_struct_0(B_421) | ~l1_struct_0(A_420))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_2584, plain, (![D_423]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_423)) | ~l1_struct_0(D_423) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_2582])).
% 7.39/2.47  tff(c_2587, plain, (![D_423]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_423)) | ~l1_struct_0(D_423) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2584])).
% 7.39/2.47  tff(c_2588, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2587])).
% 7.39/2.47  tff(c_2598, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_2588])).
% 7.39/2.47  tff(c_2602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_2598])).
% 7.39/2.47  tff(c_2604, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_2587])).
% 7.39/2.47  tff(c_2603, plain, (![D_423]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_423)) | ~l1_struct_0(D_423))), inference(splitRight, [status(thm)], [c_2587])).
% 7.39/2.47  tff(c_2605, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2603])).
% 7.39/2.47  tff(c_2610, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_2605])).
% 7.39/2.47  tff(c_2614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_2610])).
% 7.39/2.47  tff(c_2616, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_2603])).
% 7.39/2.47  tff(c_2631, plain, (![A_437, B_438, C_439, D_440]: (m1_subset_1(k2_tmap_1(A_437, B_438, C_439, D_440), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_440), u1_struct_0(B_438)))) | ~l1_struct_0(D_440) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_437), u1_struct_0(B_438)))) | ~v1_funct_2(C_439, u1_struct_0(A_437), u1_struct_0(B_438)) | ~v1_funct_1(C_439) | ~l1_struct_0(B_438) | ~l1_struct_0(A_437))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_2410, plain, (![A_385, B_386, C_387, D_388]: (v1_funct_1(k2_tmap_1(A_385, B_386, C_387, D_388)) | ~l1_struct_0(D_388) | ~m1_subset_1(C_387, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385), u1_struct_0(B_386)))) | ~v1_funct_2(C_387, u1_struct_0(A_385), u1_struct_0(B_386)) | ~v1_funct_1(C_387) | ~l1_struct_0(B_386) | ~l1_struct_0(A_385))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_2414, plain, (![D_388]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_388)) | ~l1_struct_0(D_388) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_2410])).
% 7.39/2.47  tff(c_2420, plain, (![D_388]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_388)) | ~l1_struct_0(D_388) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2414])).
% 7.39/2.47  tff(c_2421, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2420])).
% 7.39/2.47  tff(c_2424, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_2421])).
% 7.39/2.47  tff(c_2428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_2424])).
% 7.39/2.47  tff(c_2430, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_2420])).
% 7.39/2.47  tff(c_2429, plain, (![D_388]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_388)) | ~l1_struct_0(D_388))), inference(splitRight, [status(thm)], [c_2420])).
% 7.39/2.47  tff(c_2450, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2429])).
% 7.39/2.47  tff(c_2453, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_2450])).
% 7.39/2.47  tff(c_2457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_2453])).
% 7.39/2.47  tff(c_2459, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_2429])).
% 7.39/2.47  tff(c_2515, plain, (![A_407, B_408, C_409, D_410]: (m1_subset_1(k2_tmap_1(A_407, B_408, C_409, D_410), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_410), u1_struct_0(B_408)))) | ~l1_struct_0(D_410) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_407), u1_struct_0(B_408)))) | ~v1_funct_2(C_409, u1_struct_0(A_407), u1_struct_0(B_408)) | ~v1_funct_1(C_409) | ~l1_struct_0(B_408) | ~l1_struct_0(A_407))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_413, plain, (![A_179, B_180, C_181, D_182]: (v1_funct_1(k2_tmap_1(A_179, B_180, C_181, D_182)) | ~m1_pre_topc(D_182, A_179) | v2_struct_0(D_182) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_179), u1_struct_0(B_180)))) | ~v5_pre_topc(C_181, A_179, B_180) | ~v1_funct_2(C_181, u1_struct_0(A_179), u1_struct_0(B_180)) | ~v1_funct_1(C_181) | ~l1_pre_topc(B_180) | ~v2_pre_topc(B_180) | v2_struct_0(B_180) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.39/2.47  tff(c_421, plain, (![D_182]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_182)) | ~m1_pre_topc(D_182, '#skF_1') | v2_struct_0(D_182) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_413])).
% 7.39/2.47  tff(c_433, plain, (![D_182]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_182)) | ~m1_pre_topc(D_182, '#skF_1') | v2_struct_0(D_182) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_72, c_70, c_421])).
% 7.39/2.47  tff(c_434, plain, (![D_182]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_182)) | ~m1_pre_topc(D_182, '#skF_1') | v2_struct_0(D_182) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_433])).
% 7.39/2.47  tff(c_435, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_434])).
% 7.39/2.47  tff(c_56, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_170, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_228, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_170])).
% 7.39/2.47  tff(c_160, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_242, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_160])).
% 7.39/2.47  tff(c_150, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_230, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_150])).
% 7.39/2.47  tff(c_58, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_298, plain, (![A_157, B_158, C_159, D_160]: (v1_funct_1(k2_tmap_1(A_157, B_158, C_159, D_160)) | ~l1_struct_0(D_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_157), u1_struct_0(B_158)))) | ~v1_funct_2(C_159, u1_struct_0(A_157), u1_struct_0(B_158)) | ~v1_funct_1(C_159) | ~l1_struct_0(B_158) | ~l1_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_304, plain, (![D_160]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_160)) | ~l1_struct_0(D_160) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_298])).
% 7.39/2.47  tff(c_313, plain, (![D_160]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_160)) | ~l1_struct_0(D_160) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_304])).
% 7.39/2.47  tff(c_333, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_313])).
% 7.39/2.47  tff(c_336, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_333])).
% 7.39/2.47  tff(c_340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_336])).
% 7.39/2.47  tff(c_342, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_313])).
% 7.39/2.47  tff(c_341, plain, (![D_160]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_160)) | ~l1_struct_0(D_160))), inference(splitRight, [status(thm)], [c_313])).
% 7.39/2.47  tff(c_343, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_341])).
% 7.39/2.47  tff(c_346, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_343])).
% 7.39/2.47  tff(c_350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_346])).
% 7.39/2.47  tff(c_352, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_341])).
% 7.39/2.47  tff(c_366, plain, (![A_166, B_167, C_168, D_169]: (v1_funct_2(k2_tmap_1(A_166, B_167, C_168, D_169), u1_struct_0(D_169), u1_struct_0(B_167)) | ~l1_struct_0(D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166), u1_struct_0(B_167)))) | ~v1_funct_2(C_168, u1_struct_0(A_166), u1_struct_0(B_167)) | ~v1_funct_1(C_168) | ~l1_struct_0(B_167) | ~l1_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_372, plain, (![D_169]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_169), u1_struct_0(D_169), u1_struct_0('#skF_2')) | ~l1_struct_0(D_169) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_366])).
% 7.39/2.47  tff(c_381, plain, (![D_169]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_169), u1_struct_0(D_169), u1_struct_0('#skF_2')) | ~l1_struct_0(D_169))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_352, c_72, c_70, c_372])).
% 7.39/2.47  tff(c_14, plain, (![A_55, B_56, C_57, D_58]: (m1_subset_1(k2_tmap_1(A_55, B_56, C_57, D_58), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_58), u1_struct_0(B_56)))) | ~l1_struct_0(D_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_55), u1_struct_0(B_56)))) | ~v1_funct_2(C_57, u1_struct_0(A_55), u1_struct_0(B_56)) | ~v1_funct_1(C_57) | ~l1_struct_0(B_56) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.39/2.47  tff(c_351, plain, (![D_160]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_160)) | ~l1_struct_0(D_160))), inference(splitRight, [status(thm)], [c_341])).
% 7.39/2.47  tff(c_50, plain, (![A_94]: (m1_pre_topc(A_94, A_94) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_226])).
% 7.39/2.47  tff(c_582, plain, (![D_217, C_216, B_214, A_215, E_213]: (k3_tmap_1(A_215, B_214, C_216, D_217, E_213)=k2_partfun1(u1_struct_0(C_216), u1_struct_0(B_214), E_213, u1_struct_0(D_217)) | ~m1_pre_topc(D_217, C_216) | ~m1_subset_1(E_213, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_216), u1_struct_0(B_214)))) | ~v1_funct_2(E_213, u1_struct_0(C_216), u1_struct_0(B_214)) | ~v1_funct_1(E_213) | ~m1_pre_topc(D_217, A_215) | ~m1_pre_topc(C_216, A_215) | ~l1_pre_topc(B_214) | ~v2_pre_topc(B_214) | v2_struct_0(B_214) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.39/2.47  tff(c_590, plain, (![A_215, D_217]: (k3_tmap_1(A_215, '#skF_2', '#skF_1', D_217, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_217)) | ~m1_pre_topc(D_217, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_217, A_215) | ~m1_pre_topc('#skF_1', A_215) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_68, c_582])).
% 7.39/2.47  tff(c_602, plain, (![A_215, D_217]: (k3_tmap_1(A_215, '#skF_2', '#skF_1', D_217, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_217)) | ~m1_pre_topc(D_217, '#skF_1') | ~m1_pre_topc(D_217, A_215) | ~m1_pre_topc('#skF_1', A_215) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_590])).
% 7.39/2.47  tff(c_605, plain, (![A_220, D_221]: (k3_tmap_1(A_220, '#skF_2', '#skF_1', D_221, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_221)) | ~m1_pre_topc(D_221, '#skF_1') | ~m1_pre_topc(D_221, A_220) | ~m1_pre_topc('#skF_1', A_220) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(negUnitSimplification, [status(thm)], [c_78, c_602])).
% 7.39/2.47  tff(c_611, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_605])).
% 7.39/2.47  tff(c_620, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_64, c_611])).
% 7.39/2.47  tff(c_621, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_84, c_620])).
% 7.39/2.47  tff(c_626, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_621])).
% 7.39/2.47  tff(c_630, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_626])).
% 7.39/2.47  tff(c_634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_630])).
% 7.39/2.47  tff(c_636, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_621])).
% 7.39/2.47  tff(c_603, plain, (![A_215, D_217]: (k3_tmap_1(A_215, '#skF_2', '#skF_1', D_217, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_217)) | ~m1_pre_topc(D_217, '#skF_1') | ~m1_pre_topc(D_217, A_215) | ~m1_pre_topc('#skF_1', A_215) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(negUnitSimplification, [status(thm)], [c_78, c_602])).
% 7.39/2.47  tff(c_638, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_636, c_603])).
% 7.39/2.47  tff(c_651, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_636, c_638])).
% 7.39/2.47  tff(c_652, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_84, c_651])).
% 7.39/2.47  tff(c_438, plain, (![A_183, B_184, C_185, D_186]: (k2_partfun1(u1_struct_0(A_183), u1_struct_0(B_184), C_185, u1_struct_0(D_186))=k2_tmap_1(A_183, B_184, C_185, D_186) | ~m1_pre_topc(D_186, A_183) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_183), u1_struct_0(B_184)))) | ~v1_funct_2(C_185, u1_struct_0(A_183), u1_struct_0(B_184)) | ~v1_funct_1(C_185) | ~l1_pre_topc(B_184) | ~v2_pre_topc(B_184) | v2_struct_0(B_184) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.39/2.47  tff(c_446, plain, (![D_186]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_186))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_186) | ~m1_pre_topc(D_186, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_438])).
% 7.39/2.47  tff(c_458, plain, (![D_186]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_186))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_186) | ~m1_pre_topc(D_186, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_72, c_70, c_446])).
% 7.39/2.47  tff(c_459, plain, (![D_186]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_186))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_186) | ~m1_pre_topc(D_186, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_458])).
% 7.39/2.47  tff(c_704, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_652, c_459])).
% 7.39/2.47  tff(c_711, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_636, c_704])).
% 7.39/2.47  tff(c_469, plain, (![C_188, B_189, D_190, A_191]: (r2_funct_2(u1_struct_0(C_188), u1_struct_0(B_189), D_190, k3_tmap_1(A_191, B_189, C_188, C_188, D_190)) | ~m1_subset_1(D_190, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_188), u1_struct_0(B_189)))) | ~v1_funct_2(D_190, u1_struct_0(C_188), u1_struct_0(B_189)) | ~v1_funct_1(D_190) | ~m1_pre_topc(C_188, A_191) | v2_struct_0(C_188) | ~l1_pre_topc(B_189) | ~v2_pre_topc(B_189) | v2_struct_0(B_189) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_256])).
% 7.39/2.47  tff(c_477, plain, (![A_191]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_191, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_1', A_191) | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_68, c_469])).
% 7.39/2.47  tff(c_489, plain, (![A_191]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_191, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_191) | v2_struct_0('#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_477])).
% 7.39/2.47  tff(c_491, plain, (![A_192]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_192, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_192) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(negUnitSimplification, [status(thm)], [c_78, c_84, c_489])).
% 7.39/2.47  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.39/2.47  tff(c_493, plain, (![A_192]: (k3_tmap_1(A_192, '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k3_tmap_1(A_192, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_192, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_192, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_1', A_192) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(resolution, [status(thm)], [c_491, c_4])).
% 7.39/2.47  tff(c_496, plain, (![A_192]: (k3_tmap_1(A_192, '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k3_tmap_1(A_192, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_192, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_192, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_192) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_493])).
% 7.39/2.47  tff(c_719, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_711, c_496])).
% 7.39/2.47  tff(c_726, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_636, c_711, c_711, c_711, c_719])).
% 7.39/2.47  tff(c_727, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_84, c_726])).
% 7.39/2.47  tff(c_886, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_727])).
% 7.39/2.47  tff(c_889, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_351, c_886])).
% 7.39/2.47  tff(c_893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_889])).
% 7.39/2.47  tff(c_894, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_727])).
% 7.39/2.47  tff(c_929, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_894])).
% 7.39/2.47  tff(c_950, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_929])).
% 7.39/2.47  tff(c_954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_352, c_72, c_70, c_68, c_950])).
% 7.39/2.47  tff(c_955, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_894])).
% 7.39/2.47  tff(c_1008, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_955])).
% 7.39/2.47  tff(c_1012, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_381, c_1008])).
% 7.39/2.47  tff(c_1016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_1012])).
% 7.39/2.47  tff(c_1017, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_955])).
% 7.39/2.47  tff(c_140, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_261, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_140])).
% 7.39/2.47  tff(c_130, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_229, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_130])).
% 7.39/2.47  tff(c_120, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_260, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_120])).
% 7.39/2.47  tff(c_110, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_231, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_110])).
% 7.39/2.47  tff(c_100, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_262, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_100])).
% 7.39/2.47  tff(c_2220, plain, (![E_371, A_368, B_369, D_367, C_370]: (v5_pre_topc(k2_tmap_1(A_368, B_369, E_371, k1_tsep_1(A_368, C_370, D_367)), k1_tsep_1(A_368, C_370, D_367), B_369) | ~m1_subset_1(k2_tmap_1(A_368, B_369, E_371, D_367), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_367), u1_struct_0(B_369)))) | ~v5_pre_topc(k2_tmap_1(A_368, B_369, E_371, D_367), D_367, B_369) | ~v1_funct_2(k2_tmap_1(A_368, B_369, E_371, D_367), u1_struct_0(D_367), u1_struct_0(B_369)) | ~v1_funct_1(k2_tmap_1(A_368, B_369, E_371, D_367)) | ~m1_subset_1(k2_tmap_1(A_368, B_369, E_371, C_370), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_370), u1_struct_0(B_369)))) | ~v5_pre_topc(k2_tmap_1(A_368, B_369, E_371, C_370), C_370, B_369) | ~v1_funct_2(k2_tmap_1(A_368, B_369, E_371, C_370), u1_struct_0(C_370), u1_struct_0(B_369)) | ~v1_funct_1(k2_tmap_1(A_368, B_369, E_371, C_370)) | ~m1_subset_1(E_371, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_368), u1_struct_0(B_369)))) | ~v1_funct_2(E_371, u1_struct_0(A_368), u1_struct_0(B_369)) | ~v1_funct_1(E_371) | ~r4_tsep_1(A_368, C_370, D_367) | ~m1_pre_topc(D_367, A_368) | v2_struct_0(D_367) | ~m1_pre_topc(C_370, A_368) | v2_struct_0(C_370) | ~l1_pre_topc(B_369) | ~v2_pre_topc(B_369) | v2_struct_0(B_369) | ~l1_pre_topc(A_368) | ~v2_pre_topc(A_368) | v2_struct_0(A_368))), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.39/2.47  tff(c_2230, plain, (![C_370]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_370, '#skF_5')), k1_tsep_1('#skF_1', C_370, '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_370), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_370), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_370), C_370, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_370), u1_struct_0(C_370), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_370)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~r4_tsep_1('#skF_1', C_370, '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_370, '#skF_1') | v2_struct_0(C_370) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_262, c_2220])).
% 7.39/2.47  tff(c_2247, plain, (![C_370]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_370, '#skF_5')), k1_tsep_1('#skF_1', C_370, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_370), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_370), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_370), C_370, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_370), u1_struct_0(C_370), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_370)) | ~r4_tsep_1('#skF_1', C_370, '#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_370, '#skF_1') | v2_struct_0(C_370) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_60, c_72, c_70, c_68, c_229, c_260, c_231, c_2230])).
% 7.39/2.47  tff(c_2314, plain, (![C_375]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_375, '#skF_5')), k1_tsep_1('#skF_1', C_375, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_375), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_375), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_375), C_375, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_375), u1_struct_0(C_375), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_375)) | ~r4_tsep_1('#skF_1', C_375, '#skF_5') | ~m1_pre_topc(C_375, '#skF_1') | v2_struct_0(C_375))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_62, c_2247])).
% 7.39/2.47  tff(c_2335, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_261, c_2314])).
% 7.39/2.47  tff(c_2356, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_56, c_228, c_242, c_230, c_58, c_1017, c_58, c_2335])).
% 7.39/2.47  tff(c_2358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_435, c_2356])).
% 7.39/2.47  tff(c_2360, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_434])).
% 7.39/2.47  tff(c_86, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.39/2.47  tff(c_184, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_86])).
% 7.39/2.47  tff(c_194, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_184])).
% 7.39/2.47  tff(c_204, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_194])).
% 7.39/2.47  tff(c_2396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2360, c_228, c_242, c_230, c_261, c_229, c_260, c_231, c_262, c_204])).
% 7.39/2.47  tff(c_2398, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_100])).
% 7.39/2.47  tff(c_2524, plain, (~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2515, c_2398])).
% 7.39/2.47  tff(c_2530, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2430, c_2459, c_72, c_70, c_68, c_2524])).
% 7.39/2.47  tff(c_2549, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6, c_2530])).
% 7.39/2.47  tff(c_2553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_2549])).
% 7.39/2.47  tff(c_2555, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_140])).
% 7.39/2.47  tff(c_2640, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2631, c_2555])).
% 7.39/2.47  tff(c_2646, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2604, c_2616, c_72, c_70, c_68, c_2640])).
% 7.39/2.47  tff(c_2649, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_2646])).
% 7.39/2.47  tff(c_2653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_224, c_2649])).
% 7.39/2.47  tff(c_2655, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_120])).
% 7.39/2.47  tff(c_2727, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2723, c_2655])).
% 7.39/2.47  tff(c_2740, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6, c_2727])).
% 7.39/2.47  tff(c_2744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_2740])).
% 7.39/2.47  tff(c_2746, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_160])).
% 7.39/2.47  tff(c_2836, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_2832, c_2746])).
% 7.39/2.47  tff(c_2839, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_2836])).
% 7.39/2.47  tff(c_2843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_224, c_2839])).
% 7.39/2.47  tff(c_2844, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_110])).
% 7.39/2.47  tff(c_2985, plain, (![A_523, B_524, C_525, D_526]: (v5_pre_topc(k2_tmap_1(A_523, B_524, C_525, D_526), D_526, B_524) | ~m1_pre_topc(D_526, A_523) | v2_struct_0(D_526) | ~m1_subset_1(C_525, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_523), u1_struct_0(B_524)))) | ~v5_pre_topc(C_525, A_523, B_524) | ~v1_funct_2(C_525, u1_struct_0(A_523), u1_struct_0(B_524)) | ~v1_funct_1(C_525) | ~l1_pre_topc(B_524) | ~v2_pre_topc(B_524) | v2_struct_0(B_524) | ~l1_pre_topc(A_523) | ~v2_pre_topc(A_523) | v2_struct_0(A_523))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.39/2.47  tff(c_2989, plain, (![D_526]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_526), D_526, '#skF_2') | ~m1_pre_topc(D_526, '#skF_1') | v2_struct_0(D_526) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_2985])).
% 7.39/2.47  tff(c_2993, plain, (![D_526]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_526), D_526, '#skF_2') | ~m1_pre_topc(D_526, '#skF_1') | v2_struct_0(D_526) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_72, c_70, c_2844, c_2989])).
% 7.39/2.47  tff(c_2995, plain, (![D_527]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_527), D_527, '#skF_2') | ~m1_pre_topc(D_527, '#skF_1') | v2_struct_0(D_527))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_2993])).
% 7.39/2.47  tff(c_2845, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_110])).
% 7.39/2.47  tff(c_2998, plain, (~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2995, c_2845])).
% 7.39/2.47  tff(c_3001, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2998])).
% 7.39/2.47  tff(c_3003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_3001])).
% 7.39/2.47  tff(c_3004, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_150])).
% 7.39/2.47  tff(c_3160, plain, (![A_571, B_572, C_573, D_574]: (v5_pre_topc(k2_tmap_1(A_571, B_572, C_573, D_574), D_574, B_572) | ~m1_pre_topc(D_574, A_571) | v2_struct_0(D_574) | ~m1_subset_1(C_573, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_571), u1_struct_0(B_572)))) | ~v5_pre_topc(C_573, A_571, B_572) | ~v1_funct_2(C_573, u1_struct_0(A_571), u1_struct_0(B_572)) | ~v1_funct_1(C_573) | ~l1_pre_topc(B_572) | ~v2_pre_topc(B_572) | v2_struct_0(B_572) | ~l1_pre_topc(A_571) | ~v2_pre_topc(A_571) | v2_struct_0(A_571))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.39/2.47  tff(c_3164, plain, (![D_574]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_574), D_574, '#skF_2') | ~m1_pre_topc(D_574, '#skF_1') | v2_struct_0(D_574) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_3160])).
% 7.39/2.47  tff(c_3168, plain, (![D_574]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_574), D_574, '#skF_2') | ~m1_pre_topc(D_574, '#skF_1') | v2_struct_0(D_574) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_72, c_70, c_3004, c_3164])).
% 7.39/2.47  tff(c_3170, plain, (![D_575]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_575), D_575, '#skF_2') | ~m1_pre_topc(D_575, '#skF_1') | v2_struct_0(D_575))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_3168])).
% 7.39/2.47  tff(c_3005, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_150])).
% 7.39/2.47  tff(c_3173, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_3170, c_3005])).
% 7.39/2.47  tff(c_3176, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3173])).
% 7.39/2.47  tff(c_3178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_3176])).
% 7.39/2.47  tff(c_3180, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_130])).
% 7.39/2.47  tff(c_3276, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_3272, c_3180])).
% 7.39/2.47  tff(c_3279, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6, c_3276])).
% 7.39/2.47  tff(c_3283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_3279])).
% 7.39/2.47  tff(c_3285, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_170])).
% 7.39/2.47  tff(c_3384, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_3380, c_3285])).
% 7.39/2.47  tff(c_3387, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_3384])).
% 7.39/2.47  tff(c_3391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_224, c_3387])).
% 7.39/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.39/2.47  
% 7.39/2.47  Inference rules
% 7.39/2.47  ----------------------
% 7.39/2.47  #Ref     : 0
% 7.39/2.47  #Sup     : 555
% 7.39/2.47  #Fact    : 0
% 7.39/2.47  #Define  : 0
% 7.39/2.47  #Split   : 50
% 7.39/2.47  #Chain   : 0
% 7.39/2.47  #Close   : 0
% 7.39/2.47  
% 7.39/2.47  Ordering : KBO
% 7.39/2.47  
% 7.39/2.47  Simplification rules
% 7.39/2.47  ----------------------
% 7.39/2.47  #Subsume      : 175
% 7.39/2.47  #Demod        : 1851
% 7.39/2.47  #Tautology    : 206
% 7.39/2.47  #SimpNegUnit  : 173
% 7.39/2.47  #BackRed      : 8
% 7.39/2.47  
% 7.39/2.47  #Partial instantiations: 0
% 7.39/2.47  #Strategies tried      : 1
% 7.39/2.47  
% 7.39/2.47  Timing (in seconds)
% 7.39/2.47  ----------------------
% 7.39/2.47  Preprocessing        : 0.47
% 7.39/2.47  Parsing              : 0.23
% 7.39/2.47  CNF conversion       : 0.06
% 7.39/2.47  Main loop            : 1.19
% 7.39/2.48  Inferencing          : 0.39
% 7.39/2.48  Reduction            : 0.45
% 7.39/2.48  Demodulation         : 0.33
% 7.39/2.48  BG Simplification    : 0.06
% 7.39/2.48  Subsumption          : 0.25
% 7.39/2.48  Abstraction          : 0.06
% 7.39/2.48  MUC search           : 0.00
% 7.39/2.48  Cooper               : 0.00
% 7.39/2.48  Total                : 1.74
% 7.39/2.48  Index Insertion      : 0.00
% 7.39/2.48  Index Deletion       : 0.00
% 7.39/2.48  Index Matching       : 0.00
% 7.39/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
