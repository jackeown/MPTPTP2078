%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:07 EST 2020

% Result     : Theorem 7.36s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  272 (4269 expanded)
%              Number of leaves         :   38 (1705 expanded)
%              Depth                    :   21
%              Number of atoms          :  915 (48304 expanded)
%              Number of equality atoms :   27 (2017 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_337,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_151,axiom,(
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

tff(f_133,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_274,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_184,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tmap_1)).

tff(f_244,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_tmap_1)).

tff(c_82,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_62,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_212,plain,(
    ! [B_139,A_140] :
      ( l1_pre_topc(B_139)
      | ~ m1_pre_topc(B_139,A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_218,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_212])).

tff(c_224,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_218])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_2861,plain,(
    ! [A_625,B_626,C_627,D_628] :
      ( v1_funct_1(k2_tmap_1(A_625,B_626,C_627,D_628))
      | ~ l1_struct_0(D_628)
      | ~ m1_subset_1(C_627,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_625),u1_struct_0(B_626))))
      | ~ v1_funct_2(C_627,u1_struct_0(A_625),u1_struct_0(B_626))
      | ~ v1_funct_1(C_627)
      | ~ l1_struct_0(B_626)
      | ~ l1_struct_0(A_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2863,plain,(
    ! [D_628] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_628))
      | ~ l1_struct_0(D_628)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_2861])).

tff(c_2866,plain,(
    ! [D_628] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_628))
      | ~ l1_struct_0(D_628)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2863])).

tff(c_2867,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2866])).

tff(c_2870,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_2867])).

tff(c_2874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2870])).

tff(c_2875,plain,(
    ! [D_628] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_628))
      | ~ l1_struct_0(D_628) ) ),
    inference(splitRight,[status(thm)],[c_2866])).

tff(c_2877,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2875])).

tff(c_2880,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2877])).

tff(c_2884,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2880])).

tff(c_2894,plain,(
    ! [D_633] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_633))
      | ~ l1_struct_0(D_633) ) ),
    inference(splitRight,[status(thm)],[c_2875])).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_215,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_212])).

tff(c_221,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_215])).

tff(c_2763,plain,(
    ! [A_601,B_602,C_603,D_604] :
      ( v1_funct_1(k2_tmap_1(A_601,B_602,C_603,D_604))
      | ~ l1_struct_0(D_604)
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_601),u1_struct_0(B_602))))
      | ~ v1_funct_2(C_603,u1_struct_0(A_601),u1_struct_0(B_602))
      | ~ v1_funct_1(C_603)
      | ~ l1_struct_0(B_602)
      | ~ l1_struct_0(A_601) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2765,plain,(
    ! [D_604] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_604))
      | ~ l1_struct_0(D_604)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_2763])).

tff(c_2768,plain,(
    ! [D_604] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_604))
      | ~ l1_struct_0(D_604)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2765])).

tff(c_2769,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2768])).

tff(c_2772,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_2769])).

tff(c_2776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2772])).

tff(c_2777,plain,(
    ! [D_604] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_604))
      | ~ l1_struct_0(D_604) ) ),
    inference(splitRight,[status(thm)],[c_2768])).

tff(c_2786,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2777])).

tff(c_2789,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2786])).

tff(c_2793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2789])).

tff(c_2796,plain,(
    ! [D_609] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_609))
      | ~ l1_struct_0(D_609) ) ),
    inference(splitRight,[status(thm)],[c_2777])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_84,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_78,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_2319,plain,(
    ! [A_463,B_464,C_465,D_466] :
      ( v1_funct_1(k2_tmap_1(A_463,B_464,C_465,D_466))
      | ~ l1_struct_0(D_466)
      | ~ m1_subset_1(C_465,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_463),u1_struct_0(B_464))))
      | ~ v1_funct_2(C_465,u1_struct_0(A_463),u1_struct_0(B_464))
      | ~ v1_funct_1(C_465)
      | ~ l1_struct_0(B_464)
      | ~ l1_struct_0(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2321,plain,(
    ! [D_466] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_466))
      | ~ l1_struct_0(D_466)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_2319])).

tff(c_2324,plain,(
    ! [D_466] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_466))
      | ~ l1_struct_0(D_466)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2321])).

tff(c_2325,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2324])).

tff(c_2328,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_2325])).

tff(c_2332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2328])).

tff(c_2334,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2324])).

tff(c_2333,plain,(
    ! [D_466] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_466))
      | ~ l1_struct_0(D_466) ) ),
    inference(splitRight,[status(thm)],[c_2324])).

tff(c_2342,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2333])).

tff(c_2345,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2342])).

tff(c_2349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2345])).

tff(c_2351,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2333])).

tff(c_2353,plain,(
    ! [A_472,B_473,C_474,D_475] :
      ( v1_funct_2(k2_tmap_1(A_472,B_473,C_474,D_475),u1_struct_0(D_475),u1_struct_0(B_473))
      | ~ l1_struct_0(D_475)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_472),u1_struct_0(B_473))))
      | ~ v1_funct_2(C_474,u1_struct_0(A_472),u1_struct_0(B_473))
      | ~ v1_funct_1(C_474)
      | ~ l1_struct_0(B_473)
      | ~ l1_struct_0(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2355,plain,(
    ! [D_475] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_475),u1_struct_0(D_475),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_475)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_2353])).

tff(c_2359,plain,(
    ! [D_476] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_476),u1_struct_0(D_476),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_2351,c_74,c_72,c_2355])).

tff(c_2206,plain,(
    ! [A_430,B_431,C_432,D_433] :
      ( v1_funct_1(k2_tmap_1(A_430,B_431,C_432,D_433))
      | ~ l1_struct_0(D_433)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_430),u1_struct_0(B_431))))
      | ~ v1_funct_2(C_432,u1_struct_0(A_430),u1_struct_0(B_431))
      | ~ v1_funct_1(C_432)
      | ~ l1_struct_0(B_431)
      | ~ l1_struct_0(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2208,plain,(
    ! [D_433] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_433))
      | ~ l1_struct_0(D_433)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_2206])).

tff(c_2211,plain,(
    ! [D_433] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_433))
      | ~ l1_struct_0(D_433)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2208])).

tff(c_2219,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2211])).

tff(c_2222,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_2219])).

tff(c_2226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2222])).

tff(c_2228,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2211])).

tff(c_2227,plain,(
    ! [D_433] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_433))
      | ~ l1_struct_0(D_433) ) ),
    inference(splitRight,[status(thm)],[c_2211])).

tff(c_2229,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2227])).

tff(c_2232,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2229])).

tff(c_2236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2232])).

tff(c_2238,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2227])).

tff(c_2240,plain,(
    ! [A_439,B_440,C_441,D_442] :
      ( v1_funct_2(k2_tmap_1(A_439,B_440,C_441,D_442),u1_struct_0(D_442),u1_struct_0(B_440))
      | ~ l1_struct_0(D_442)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_439),u1_struct_0(B_440))))
      | ~ v1_funct_2(C_441,u1_struct_0(A_439),u1_struct_0(B_440))
      | ~ v1_funct_1(C_441)
      | ~ l1_struct_0(B_440)
      | ~ l1_struct_0(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2242,plain,(
    ! [D_442] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_442),u1_struct_0(D_442),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_442)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_2240])).

tff(c_2246,plain,(
    ! [D_443] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_443),u1_struct_0(D_443),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2228,c_2238,c_74,c_72,c_2242])).

tff(c_2092,plain,(
    ! [A_397,B_398,C_399,D_400] :
      ( v1_funct_1(k2_tmap_1(A_397,B_398,C_399,D_400))
      | ~ l1_struct_0(D_400)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_397),u1_struct_0(B_398))))
      | ~ v1_funct_2(C_399,u1_struct_0(A_397),u1_struct_0(B_398))
      | ~ v1_funct_1(C_399)
      | ~ l1_struct_0(B_398)
      | ~ l1_struct_0(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2094,plain,(
    ! [D_400] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_400))
      | ~ l1_struct_0(D_400)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_2092])).

tff(c_2097,plain,(
    ! [D_400] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_400))
      | ~ l1_struct_0(D_400)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2094])).

tff(c_2098,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2097])).

tff(c_2101,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_2098])).

tff(c_2105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2101])).

tff(c_2107,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2097])).

tff(c_2106,plain,(
    ! [D_400] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_400))
      | ~ l1_struct_0(D_400) ) ),
    inference(splitRight,[status(thm)],[c_2097])).

tff(c_2108,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2106])).

tff(c_2111,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_2108])).

tff(c_2115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2111])).

tff(c_2117,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2106])).

tff(c_2135,plain,(
    ! [A_411,B_412,C_413,D_414] :
      ( m1_subset_1(k2_tmap_1(A_411,B_412,C_413,D_414),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_414),u1_struct_0(B_412))))
      | ~ l1_struct_0(D_414)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_411),u1_struct_0(B_412))))
      | ~ v1_funct_2(C_413,u1_struct_0(A_411),u1_struct_0(B_412))
      | ~ v1_funct_1(C_413)
      | ~ l1_struct_0(B_412)
      | ~ l1_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1953,plain,(
    ! [A_364,B_365,C_366,D_367] :
      ( v1_funct_1(k2_tmap_1(A_364,B_365,C_366,D_367))
      | ~ l1_struct_0(D_367)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_364),u1_struct_0(B_365))))
      | ~ v1_funct_2(C_366,u1_struct_0(A_364),u1_struct_0(B_365))
      | ~ v1_funct_1(C_366)
      | ~ l1_struct_0(B_365)
      | ~ l1_struct_0(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1957,plain,(
    ! [D_367] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_367))
      | ~ l1_struct_0(D_367)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_1953])).

tff(c_1963,plain,(
    ! [D_367] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_367))
      | ~ l1_struct_0(D_367)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1957])).

tff(c_1964,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1963])).

tff(c_1967,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_1964])).

tff(c_1971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1967])).

tff(c_1973,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1963])).

tff(c_1972,plain,(
    ! [D_367] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_367))
      | ~ l1_struct_0(D_367) ) ),
    inference(splitRight,[status(thm)],[c_1963])).

tff(c_1987,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1972])).

tff(c_1990,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_1987])).

tff(c_1994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1990])).

tff(c_1996,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1972])).

tff(c_2022,plain,(
    ! [A_378,B_379,C_380,D_381] :
      ( m1_subset_1(k2_tmap_1(A_378,B_379,C_380,D_381),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_381),u1_struct_0(B_379))))
      | ~ l1_struct_0(D_381)
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_378),u1_struct_0(B_379))))
      | ~ v1_funct_2(C_380,u1_struct_0(A_378),u1_struct_0(B_379))
      | ~ v1_funct_1(C_380)
      | ~ l1_struct_0(B_379)
      | ~ l1_struct_0(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_172,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_226,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_162,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_230,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_152,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_228,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_142,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_231,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_132,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_225,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_122,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_229,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_112,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_227,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_102,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_232,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_88,plain,
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
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_186,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_88])).

tff(c_196,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_186])).

tff(c_206,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_196])).

tff(c_250,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_230,c_228,c_231,c_225,c_229,c_227,c_232,c_206])).

tff(c_58,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_282,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( v1_funct_1(k2_tmap_1(A_153,B_154,C_155,D_156))
      | ~ l1_struct_0(D_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_153),u1_struct_0(B_154))))
      | ~ v1_funct_2(C_155,u1_struct_0(A_153),u1_struct_0(B_154))
      | ~ v1_funct_1(C_155)
      | ~ l1_struct_0(B_154)
      | ~ l1_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_288,plain,(
    ! [D_156] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_156))
      | ~ l1_struct_0(D_156)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_282])).

tff(c_297,plain,(
    ! [D_156] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_156))
      | ~ l1_struct_0(D_156)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_288])).

tff(c_298,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_301,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_298])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_301])).

tff(c_307,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_306,plain,(
    ! [D_156] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_156))
      | ~ l1_struct_0(D_156) ) ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_308,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_311,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_308])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_311])).

tff(c_317,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_371,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( v1_funct_2(k2_tmap_1(A_167,B_168,C_169,D_170),u1_struct_0(D_170),u1_struct_0(B_168))
      | ~ l1_struct_0(D_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_167),u1_struct_0(B_168))))
      | ~ v1_funct_2(C_169,u1_struct_0(A_167),u1_struct_0(B_168))
      | ~ v1_funct_1(C_169)
      | ~ l1_struct_0(B_168)
      | ~ l1_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_377,plain,(
    ! [D_170] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_170),u1_struct_0(D_170),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_170)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_371])).

tff(c_386,plain,(
    ! [D_170] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_170),u1_struct_0(D_170),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_317,c_74,c_72,c_377])).

tff(c_316,plain,(
    ! [D_156] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_156))
      | ~ l1_struct_0(D_156) ) ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_60,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_337])).

tff(c_265,plain,(
    ! [A_150,B_151,C_152] :
      ( m1_pre_topc(k1_tsep_1(A_150,B_151,C_152),A_150)
      | ~ m1_pre_topc(C_152,A_150)
      | v2_struct_0(C_152)
      | ~ m1_pre_topc(B_151,A_150)
      | v2_struct_0(B_151)
      | ~ l1_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_271,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_265])).

tff(c_274,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_66,c_62,c_271])).

tff(c_275,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_68,c_64,c_274])).

tff(c_568,plain,(
    ! [C_215,A_214,E_212,D_216,B_213] :
      ( k3_tmap_1(A_214,B_213,C_215,D_216,E_212) = k2_partfun1(u1_struct_0(C_215),u1_struct_0(B_213),E_212,u1_struct_0(D_216))
      | ~ m1_pre_topc(D_216,C_215)
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_215),u1_struct_0(B_213))))
      | ~ v1_funct_2(E_212,u1_struct_0(C_215),u1_struct_0(B_213))
      | ~ v1_funct_1(E_212)
      | ~ m1_pre_topc(D_216,A_214)
      | ~ m1_pre_topc(C_215,A_214)
      | ~ l1_pre_topc(B_213)
      | ~ v2_pre_topc(B_213)
      | v2_struct_0(B_213)
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_576,plain,(
    ! [A_214,D_216] :
      ( k3_tmap_1(A_214,'#skF_2','#skF_1',D_216,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_216))
      | ~ m1_pre_topc(D_216,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_216,A_214)
      | ~ m1_pre_topc('#skF_1',A_214)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(resolution,[status(thm)],[c_70,c_568])).

tff(c_588,plain,(
    ! [A_214,D_216] :
      ( k3_tmap_1(A_214,'#skF_2','#skF_1',D_216,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_216))
      | ~ m1_pre_topc(D_216,'#skF_1')
      | ~ m1_pre_topc(D_216,A_214)
      | ~ m1_pre_topc('#skF_1',A_214)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_576])).

tff(c_591,plain,(
    ! [A_219,D_220] :
      ( k3_tmap_1(A_219,'#skF_2','#skF_1',D_220,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_220))
      | ~ m1_pre_topc(D_220,'#skF_1')
      | ~ m1_pre_topc(D_220,A_219)
      | ~ m1_pre_topc('#skF_1',A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_588])).

tff(c_593,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_275,c_591])).

tff(c_602,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_275,c_593])).

tff(c_603,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_602])).

tff(c_424,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k2_partfun1(u1_struct_0(A_182),u1_struct_0(B_183),C_184,u1_struct_0(D_185)) = k2_tmap_1(A_182,B_183,C_184,D_185)
      | ~ m1_pre_topc(D_185,A_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_182),u1_struct_0(B_183))))
      | ~ v1_funct_2(C_184,u1_struct_0(A_182),u1_struct_0(B_183))
      | ~ v1_funct_1(C_184)
      | ~ l1_pre_topc(B_183)
      | ~ v2_pre_topc(B_183)
      | v2_struct_0(B_183)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_432,plain,(
    ! [D_185] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_185)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_185)
      | ~ m1_pre_topc(D_185,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_424])).

tff(c_444,plain,(
    ! [D_185] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_185)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_185)
      | ~ m1_pre_topc(D_185,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_78,c_76,c_74,c_72,c_432])).

tff(c_445,plain,(
    ! [D_185] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_185)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_185)
      | ~ m1_pre_topc(D_185,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_444])).

tff(c_616,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_445])).

tff(c_623,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_616])).

tff(c_455,plain,(
    ! [C_187,B_188,D_189,A_190] :
      ( r2_funct_2(u1_struct_0(C_187),u1_struct_0(B_188),D_189,k3_tmap_1(A_190,B_188,C_187,C_187,D_189))
      | ~ m1_subset_1(D_189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_187),u1_struct_0(B_188))))
      | ~ v1_funct_2(D_189,u1_struct_0(C_187),u1_struct_0(B_188))
      | ~ v1_funct_1(D_189)
      | ~ m1_pre_topc(C_187,A_190)
      | v2_struct_0(C_187)
      | ~ l1_pre_topc(B_188)
      | ~ v2_pre_topc(B_188)
      | v2_struct_0(B_188)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_463,plain,(
    ! [A_190] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_190,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_1',A_190)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_70,c_455])).

tff(c_475,plain,(
    ! [A_190] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_190,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_190)
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_463])).

tff(c_477,plain,(
    ! [A_191] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_191,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_86,c_475])).

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

tff(c_479,plain,(
    ! [A_191] :
      ( k3_tmap_1(A_191,'#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
      | ~ m1_subset_1(k3_tmap_1(A_191,'#skF_2','#skF_1','#skF_1','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_191,'#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_191,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_1',A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_477,c_4])).

tff(c_482,plain,(
    ! [A_191] :
      ( k3_tmap_1(A_191,'#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
      | ~ m1_subset_1(k3_tmap_1(A_191,'#skF_2','#skF_1','#skF_1','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_191,'#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_191,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_479])).

tff(c_645,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_482])).

tff(c_652,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_275,c_623,c_623,c_623,c_645])).

tff(c_653,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_652])).

tff(c_734,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_653])).

tff(c_737,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_316,c_734])).

tff(c_741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_737])).

tff(c_743,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_20,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( m1_subset_1(k2_tmap_1(A_58,B_59,C_60,D_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_61),u1_struct_0(B_59))))
      | ~ l1_struct_0(D_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58),u1_struct_0(B_59))))
      | ~ v1_funct_2(C_60,u1_struct_0(A_58),u1_struct_0(B_59))
      | ~ v1_funct_1(C_60)
      | ~ l1_struct_0(B_59)
      | ~ l1_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_742,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_784,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_742])).

tff(c_787,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_784])).

tff(c_791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_317,c_74,c_72,c_70,c_787])).

tff(c_793,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_742])).

tff(c_30,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( v1_funct_1(k2_tmap_1(A_62,B_63,C_64,D_65))
      | ~ m1_pre_topc(D_65,A_62)
      | v2_struct_0(D_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_62),u1_struct_0(B_63))))
      | ~ v5_pre_topc(C_64,A_62,B_63)
      | ~ v1_funct_2(C_64,u1_struct_0(A_62),u1_struct_0(B_63))
      | ~ v1_funct_1(C_64)
      | ~ l1_pre_topc(B_63)
      | ~ v2_pre_topc(B_63)
      | v2_struct_0(B_63)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_805,plain,(
    ! [D_65] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),D_65))
      | ~ m1_pre_topc(D_65,'#skF_1')
      | v2_struct_0(D_65)
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),'#skF_1','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_793,c_30])).

tff(c_834,plain,(
    ! [D_65] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),D_65))
      | ~ m1_pre_topc(D_65,'#skF_1')
      | v2_struct_0(D_65)
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),'#skF_1','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_78,c_76,c_743,c_805])).

tff(c_835,plain,(
    ! [D_65] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),D_65))
      | ~ m1_pre_topc(D_65,'#skF_1')
      | v2_struct_0(D_65)
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),'#skF_1','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_834])).

tff(c_845,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_835])).

tff(c_848,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_386,c_845])).

tff(c_852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_848])).

tff(c_854,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_792,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_742])).

tff(c_862,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_792])).

tff(c_1822,plain,(
    ! [E_345,D_343,A_344,B_347,C_346] :
      ( v5_pre_topc(k2_tmap_1(A_344,B_347,E_345,k1_tsep_1(A_344,C_346,D_343)),k1_tsep_1(A_344,C_346,D_343),B_347)
      | ~ m1_subset_1(k2_tmap_1(A_344,B_347,E_345,D_343),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_343),u1_struct_0(B_347))))
      | ~ v5_pre_topc(k2_tmap_1(A_344,B_347,E_345,D_343),D_343,B_347)
      | ~ v1_funct_2(k2_tmap_1(A_344,B_347,E_345,D_343),u1_struct_0(D_343),u1_struct_0(B_347))
      | ~ v1_funct_1(k2_tmap_1(A_344,B_347,E_345,D_343))
      | ~ m1_subset_1(k2_tmap_1(A_344,B_347,E_345,C_346),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346),u1_struct_0(B_347))))
      | ~ v5_pre_topc(k2_tmap_1(A_344,B_347,E_345,C_346),C_346,B_347)
      | ~ v1_funct_2(k2_tmap_1(A_344,B_347,E_345,C_346),u1_struct_0(C_346),u1_struct_0(B_347))
      | ~ v1_funct_1(k2_tmap_1(A_344,B_347,E_345,C_346))
      | ~ m1_subset_1(E_345,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_344),u1_struct_0(B_347))))
      | ~ v1_funct_2(E_345,u1_struct_0(A_344),u1_struct_0(B_347))
      | ~ v1_funct_1(E_345)
      | ~ r4_tsep_1(A_344,C_346,D_343)
      | ~ m1_pre_topc(D_343,A_344)
      | v2_struct_0(D_343)
      | ~ m1_pre_topc(C_346,A_344)
      | v2_struct_0(C_346)
      | ~ l1_pre_topc(B_347)
      | ~ v2_pre_topc(B_347)
      | v2_struct_0(B_347)
      | ~ l1_pre_topc(A_344)
      | ~ v2_pre_topc(A_344)
      | v2_struct_0(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1832,plain,(
    ! [C_346] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_346,'#skF_5')),k1_tsep_1('#skF_1',C_346,'#skF_5'),'#skF_2')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_346),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_346),C_346,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_346),u1_struct_0(C_346),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_346))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ r4_tsep_1('#skF_1',C_346,'#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_346,'#skF_1')
      | v2_struct_0(C_346)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_232,c_1822])).

tff(c_1849,plain,(
    ! [C_346] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_346,'#skF_5')),k1_tsep_1('#skF_1',C_346,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_346),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_346),C_346,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_346),u1_struct_0(C_346),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_346))
      | ~ r4_tsep_1('#skF_1',C_346,'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_346,'#skF_1')
      | v2_struct_0(C_346)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_78,c_76,c_62,c_74,c_72,c_70,c_225,c_229,c_227,c_1832])).

tff(c_1857,plain,(
    ! [C_348] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_348,'#skF_5')),k1_tsep_1('#skF_1',C_348,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_348),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_348),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_348),C_348,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_348),u1_struct_0(C_348),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_348))
      | ~ r4_tsep_1('#skF_1',C_348,'#skF_5')
      | ~ m1_pre_topc(C_348,'#skF_1')
      | v2_struct_0(C_348) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_64,c_1849])).

tff(c_1878,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_231,c_1857])).

tff(c_1899,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_58,c_226,c_230,c_228,c_862,c_60,c_60,c_1878])).

tff(c_1901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_250,c_1899])).

tff(c_1903,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_2031,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2022,c_1903])).

tff(c_2037,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1973,c_1996,c_74,c_72,c_70,c_2031])).

tff(c_2040,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_2037])).

tff(c_2044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_2040])).

tff(c_2046,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_2144,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2135,c_2046])).

tff(c_2150,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2107,c_2117,c_74,c_72,c_70,c_2144])).

tff(c_2153,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2150])).

tff(c_2157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_2153])).

tff(c_2159,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_2250,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2246,c_2159])).

tff(c_2263,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2250])).

tff(c_2267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_2263])).

tff(c_2269,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_2363,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2359,c_2269])).

tff(c_2366,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_2363])).

tff(c_2370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_2366])).

tff(c_2371,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_2504,plain,(
    ! [A_520,B_521,C_522,D_523] :
      ( v5_pre_topc(k2_tmap_1(A_520,B_521,C_522,D_523),D_523,B_521)
      | ~ m1_pre_topc(D_523,A_520)
      | v2_struct_0(D_523)
      | ~ m1_subset_1(C_522,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_520),u1_struct_0(B_521))))
      | ~ v5_pre_topc(C_522,A_520,B_521)
      | ~ v1_funct_2(C_522,u1_struct_0(A_520),u1_struct_0(B_521))
      | ~ v1_funct_1(C_522)
      | ~ l1_pre_topc(B_521)
      | ~ v2_pre_topc(B_521)
      | v2_struct_0(B_521)
      | ~ l1_pre_topc(A_520)
      | ~ v2_pre_topc(A_520)
      | v2_struct_0(A_520) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2508,plain,(
    ! [D_523] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_523),D_523,'#skF_2')
      | ~ m1_pre_topc(D_523,'#skF_1')
      | v2_struct_0(D_523)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_2504])).

tff(c_2512,plain,(
    ! [D_523] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_523),D_523,'#skF_2')
      | ~ m1_pre_topc(D_523,'#skF_1')
      | v2_struct_0(D_523)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_78,c_76,c_74,c_72,c_2371,c_2508])).

tff(c_2524,plain,(
    ! [D_528] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_528),D_528,'#skF_2')
      | ~ m1_pre_topc(D_528,'#skF_1')
      | v2_struct_0(D_528) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_2512])).

tff(c_2372,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_2527,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2524,c_2372])).

tff(c_2530,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2527])).

tff(c_2532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2530])).

tff(c_2533,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_2690,plain,(
    ! [A_581,B_582,C_583,D_584] :
      ( v5_pre_topc(k2_tmap_1(A_581,B_582,C_583,D_584),D_584,B_582)
      | ~ m1_pre_topc(D_584,A_581)
      | v2_struct_0(D_584)
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_581),u1_struct_0(B_582))))
      | ~ v5_pre_topc(C_583,A_581,B_582)
      | ~ v1_funct_2(C_583,u1_struct_0(A_581),u1_struct_0(B_582))
      | ~ v1_funct_1(C_583)
      | ~ l1_pre_topc(B_582)
      | ~ v2_pre_topc(B_582)
      | v2_struct_0(B_582)
      | ~ l1_pre_topc(A_581)
      | ~ v2_pre_topc(A_581)
      | v2_struct_0(A_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2694,plain,(
    ! [D_584] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_584),D_584,'#skF_2')
      | ~ m1_pre_topc(D_584,'#skF_1')
      | v2_struct_0(D_584)
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_2690])).

tff(c_2698,plain,(
    ! [D_584] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_584),D_584,'#skF_2')
      | ~ m1_pre_topc(D_584,'#skF_1')
      | v2_struct_0(D_584)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_78,c_76,c_74,c_72,c_2533,c_2694])).

tff(c_2700,plain,(
    ! [D_585] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_585),D_585,'#skF_2')
      | ~ m1_pre_topc(D_585,'#skF_1')
      | v2_struct_0(D_585) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_2698])).

tff(c_2534,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_2703,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2700,c_2534])).

tff(c_2706,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2703])).

tff(c_2708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2706])).

tff(c_2710,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_2800,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2796,c_2710])).

tff(c_2803,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2800])).

tff(c_2807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_2803])).

tff(c_2809,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_2898,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2894,c_2809])).

tff(c_2901,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_2898])).

tff(c_2905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_2901])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.36/2.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.52  
% 7.74/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.52  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.74/2.52  
% 7.74/2.52  %Foreground sorts:
% 7.74/2.52  
% 7.74/2.52  
% 7.74/2.52  %Background operators:
% 7.74/2.52  
% 7.74/2.52  
% 7.74/2.52  %Foreground operators:
% 7.74/2.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.74/2.52  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 7.74/2.52  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.74/2.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.74/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.74/2.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.74/2.52  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 7.74/2.52  tff('#skF_5', type, '#skF_5': $i).
% 7.74/2.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.74/2.52  tff('#skF_2', type, '#skF_2': $i).
% 7.74/2.52  tff('#skF_3', type, '#skF_3': $i).
% 7.74/2.52  tff('#skF_1', type, '#skF_1': $i).
% 7.74/2.52  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.74/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.74/2.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.74/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.74/2.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.74/2.52  tff('#skF_4', type, '#skF_4': $i).
% 7.74/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.74/2.52  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.74/2.52  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.74/2.52  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.74/2.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.74/2.52  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.74/2.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.74/2.52  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.74/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.74/2.52  
% 7.74/2.56  tff(f_337, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (((A = k1_tsep_1(A, D, E)) & r4_tsep_1(A, D, E)) => ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, C, E))) & v1_funct_2(k2_tmap_1(A, B, C, E), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, E), E, B)) & m1_subset_1(k2_tmap_1(A, B, C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_tmap_1)).
% 7.74/2.56  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.74/2.56  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.74/2.56  tff(f_151, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 7.74/2.56  tff(f_133, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 7.74/2.56  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 7.74/2.56  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.74/2.56  tff(f_274, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 7.74/2.56  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.74/2.56  tff(f_184, axiom, (![A, B, C, D]: ((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tmap_1)).
% 7.74/2.56  tff(f_244, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_funct_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D))) & v1_funct_2(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_tsep_1(A, C, D), B)) & m1_subset_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, E, C)) & v1_funct_2(k2_tmap_1(A, B, E, C), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, C), C, B)) & m1_subset_1(k2_tmap_1(A, B, E, C), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, E, D))) & v1_funct_2(k2_tmap_1(A, B, E, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, E, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_tmap_1)).
% 7.74/2.56  tff(c_82, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_62, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_212, plain, (![B_139, A_140]: (l1_pre_topc(B_139) | ~m1_pre_topc(B_139, A_140) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.74/2.56  tff(c_218, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_212])).
% 7.74/2.56  tff(c_224, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_218])).
% 7.74/2.56  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.74/2.56  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_72, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_2861, plain, (![A_625, B_626, C_627, D_628]: (v1_funct_1(k2_tmap_1(A_625, B_626, C_627, D_628)) | ~l1_struct_0(D_628) | ~m1_subset_1(C_627, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_625), u1_struct_0(B_626)))) | ~v1_funct_2(C_627, u1_struct_0(A_625), u1_struct_0(B_626)) | ~v1_funct_1(C_627) | ~l1_struct_0(B_626) | ~l1_struct_0(A_625))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_2863, plain, (![D_628]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_628)) | ~l1_struct_0(D_628) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_2861])).
% 7.74/2.56  tff(c_2866, plain, (![D_628]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_628)) | ~l1_struct_0(D_628) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2863])).
% 7.74/2.56  tff(c_2867, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2866])).
% 7.74/2.56  tff(c_2870, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_2867])).
% 7.74/2.56  tff(c_2874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_2870])).
% 7.74/2.56  tff(c_2875, plain, (![D_628]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_628)) | ~l1_struct_0(D_628))), inference(splitRight, [status(thm)], [c_2866])).
% 7.74/2.56  tff(c_2877, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2875])).
% 7.74/2.56  tff(c_2880, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_2877])).
% 7.74/2.56  tff(c_2884, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_2880])).
% 7.74/2.56  tff(c_2894, plain, (![D_633]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_633)) | ~l1_struct_0(D_633))), inference(splitRight, [status(thm)], [c_2875])).
% 7.74/2.56  tff(c_66, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_215, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_212])).
% 7.74/2.56  tff(c_221, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_215])).
% 7.74/2.56  tff(c_2763, plain, (![A_601, B_602, C_603, D_604]: (v1_funct_1(k2_tmap_1(A_601, B_602, C_603, D_604)) | ~l1_struct_0(D_604) | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_601), u1_struct_0(B_602)))) | ~v1_funct_2(C_603, u1_struct_0(A_601), u1_struct_0(B_602)) | ~v1_funct_1(C_603) | ~l1_struct_0(B_602) | ~l1_struct_0(A_601))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_2765, plain, (![D_604]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_604)) | ~l1_struct_0(D_604) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_2763])).
% 7.74/2.56  tff(c_2768, plain, (![D_604]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_604)) | ~l1_struct_0(D_604) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2765])).
% 7.74/2.56  tff(c_2769, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2768])).
% 7.74/2.56  tff(c_2772, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_2769])).
% 7.74/2.56  tff(c_2776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_2772])).
% 7.74/2.56  tff(c_2777, plain, (![D_604]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_604)) | ~l1_struct_0(D_604))), inference(splitRight, [status(thm)], [c_2768])).
% 7.74/2.56  tff(c_2786, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2777])).
% 7.74/2.56  tff(c_2789, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_2786])).
% 7.74/2.56  tff(c_2793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_2789])).
% 7.74/2.56  tff(c_2796, plain, (![D_609]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_609)) | ~l1_struct_0(D_609))), inference(splitRight, [status(thm)], [c_2777])).
% 7.74/2.56  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_86, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_84, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_78, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_2319, plain, (![A_463, B_464, C_465, D_466]: (v1_funct_1(k2_tmap_1(A_463, B_464, C_465, D_466)) | ~l1_struct_0(D_466) | ~m1_subset_1(C_465, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_463), u1_struct_0(B_464)))) | ~v1_funct_2(C_465, u1_struct_0(A_463), u1_struct_0(B_464)) | ~v1_funct_1(C_465) | ~l1_struct_0(B_464) | ~l1_struct_0(A_463))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_2321, plain, (![D_466]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_466)) | ~l1_struct_0(D_466) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_2319])).
% 7.74/2.56  tff(c_2324, plain, (![D_466]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_466)) | ~l1_struct_0(D_466) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2321])).
% 7.74/2.56  tff(c_2325, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2324])).
% 7.74/2.56  tff(c_2328, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_2325])).
% 7.74/2.56  tff(c_2332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_2328])).
% 7.74/2.56  tff(c_2334, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_2324])).
% 7.74/2.56  tff(c_2333, plain, (![D_466]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_466)) | ~l1_struct_0(D_466))), inference(splitRight, [status(thm)], [c_2324])).
% 7.74/2.56  tff(c_2342, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2333])).
% 7.74/2.56  tff(c_2345, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_2342])).
% 7.74/2.56  tff(c_2349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_2345])).
% 7.74/2.56  tff(c_2351, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_2333])).
% 7.74/2.56  tff(c_2353, plain, (![A_472, B_473, C_474, D_475]: (v1_funct_2(k2_tmap_1(A_472, B_473, C_474, D_475), u1_struct_0(D_475), u1_struct_0(B_473)) | ~l1_struct_0(D_475) | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_472), u1_struct_0(B_473)))) | ~v1_funct_2(C_474, u1_struct_0(A_472), u1_struct_0(B_473)) | ~v1_funct_1(C_474) | ~l1_struct_0(B_473) | ~l1_struct_0(A_472))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_2355, plain, (![D_475]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_475), u1_struct_0(D_475), u1_struct_0('#skF_2')) | ~l1_struct_0(D_475) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_2353])).
% 7.74/2.56  tff(c_2359, plain, (![D_476]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_476), u1_struct_0(D_476), u1_struct_0('#skF_2')) | ~l1_struct_0(D_476))), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_2351, c_74, c_72, c_2355])).
% 7.74/2.56  tff(c_2206, plain, (![A_430, B_431, C_432, D_433]: (v1_funct_1(k2_tmap_1(A_430, B_431, C_432, D_433)) | ~l1_struct_0(D_433) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_430), u1_struct_0(B_431)))) | ~v1_funct_2(C_432, u1_struct_0(A_430), u1_struct_0(B_431)) | ~v1_funct_1(C_432) | ~l1_struct_0(B_431) | ~l1_struct_0(A_430))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_2208, plain, (![D_433]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_433)) | ~l1_struct_0(D_433) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_2206])).
% 7.74/2.56  tff(c_2211, plain, (![D_433]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_433)) | ~l1_struct_0(D_433) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2208])).
% 7.74/2.56  tff(c_2219, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2211])).
% 7.74/2.56  tff(c_2222, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_2219])).
% 7.74/2.56  tff(c_2226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_2222])).
% 7.74/2.56  tff(c_2228, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_2211])).
% 7.74/2.56  tff(c_2227, plain, (![D_433]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_433)) | ~l1_struct_0(D_433))), inference(splitRight, [status(thm)], [c_2211])).
% 7.74/2.56  tff(c_2229, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2227])).
% 7.74/2.56  tff(c_2232, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_2229])).
% 7.74/2.56  tff(c_2236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_2232])).
% 7.74/2.56  tff(c_2238, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_2227])).
% 7.74/2.56  tff(c_2240, plain, (![A_439, B_440, C_441, D_442]: (v1_funct_2(k2_tmap_1(A_439, B_440, C_441, D_442), u1_struct_0(D_442), u1_struct_0(B_440)) | ~l1_struct_0(D_442) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_439), u1_struct_0(B_440)))) | ~v1_funct_2(C_441, u1_struct_0(A_439), u1_struct_0(B_440)) | ~v1_funct_1(C_441) | ~l1_struct_0(B_440) | ~l1_struct_0(A_439))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_2242, plain, (![D_442]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_442), u1_struct_0(D_442), u1_struct_0('#skF_2')) | ~l1_struct_0(D_442) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_2240])).
% 7.74/2.56  tff(c_2246, plain, (![D_443]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_443), u1_struct_0(D_443), u1_struct_0('#skF_2')) | ~l1_struct_0(D_443))), inference(demodulation, [status(thm), theory('equality')], [c_2228, c_2238, c_74, c_72, c_2242])).
% 7.74/2.56  tff(c_2092, plain, (![A_397, B_398, C_399, D_400]: (v1_funct_1(k2_tmap_1(A_397, B_398, C_399, D_400)) | ~l1_struct_0(D_400) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_397), u1_struct_0(B_398)))) | ~v1_funct_2(C_399, u1_struct_0(A_397), u1_struct_0(B_398)) | ~v1_funct_1(C_399) | ~l1_struct_0(B_398) | ~l1_struct_0(A_397))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_2094, plain, (![D_400]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_400)) | ~l1_struct_0(D_400) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_2092])).
% 7.74/2.56  tff(c_2097, plain, (![D_400]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_400)) | ~l1_struct_0(D_400) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2094])).
% 7.74/2.56  tff(c_2098, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2097])).
% 7.74/2.56  tff(c_2101, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_2098])).
% 7.74/2.56  tff(c_2105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_2101])).
% 7.74/2.56  tff(c_2107, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_2097])).
% 7.74/2.56  tff(c_2106, plain, (![D_400]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_400)) | ~l1_struct_0(D_400))), inference(splitRight, [status(thm)], [c_2097])).
% 7.74/2.56  tff(c_2108, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2106])).
% 7.74/2.56  tff(c_2111, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_2108])).
% 7.74/2.56  tff(c_2115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_2111])).
% 7.74/2.56  tff(c_2117, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_2106])).
% 7.74/2.56  tff(c_2135, plain, (![A_411, B_412, C_413, D_414]: (m1_subset_1(k2_tmap_1(A_411, B_412, C_413, D_414), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_414), u1_struct_0(B_412)))) | ~l1_struct_0(D_414) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_411), u1_struct_0(B_412)))) | ~v1_funct_2(C_413, u1_struct_0(A_411), u1_struct_0(B_412)) | ~v1_funct_1(C_413) | ~l1_struct_0(B_412) | ~l1_struct_0(A_411))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_1953, plain, (![A_364, B_365, C_366, D_367]: (v1_funct_1(k2_tmap_1(A_364, B_365, C_366, D_367)) | ~l1_struct_0(D_367) | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_364), u1_struct_0(B_365)))) | ~v1_funct_2(C_366, u1_struct_0(A_364), u1_struct_0(B_365)) | ~v1_funct_1(C_366) | ~l1_struct_0(B_365) | ~l1_struct_0(A_364))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_1957, plain, (![D_367]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_367)) | ~l1_struct_0(D_367) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_1953])).
% 7.74/2.56  tff(c_1963, plain, (![D_367]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_367)) | ~l1_struct_0(D_367) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1957])).
% 7.74/2.56  tff(c_1964, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1963])).
% 7.74/2.56  tff(c_1967, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_1964])).
% 7.74/2.56  tff(c_1971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_1967])).
% 7.74/2.56  tff(c_1973, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1963])).
% 7.74/2.56  tff(c_1972, plain, (![D_367]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_367)) | ~l1_struct_0(D_367))), inference(splitRight, [status(thm)], [c_1963])).
% 7.74/2.56  tff(c_1987, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1972])).
% 7.74/2.56  tff(c_1990, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_1987])).
% 7.74/2.56  tff(c_1994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_1990])).
% 7.74/2.56  tff(c_1996, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1972])).
% 7.74/2.56  tff(c_2022, plain, (![A_378, B_379, C_380, D_381]: (m1_subset_1(k2_tmap_1(A_378, B_379, C_380, D_381), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_381), u1_struct_0(B_379)))) | ~l1_struct_0(D_381) | ~m1_subset_1(C_380, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_378), u1_struct_0(B_379)))) | ~v1_funct_2(C_380, u1_struct_0(A_378), u1_struct_0(B_379)) | ~v1_funct_1(C_380) | ~l1_struct_0(B_379) | ~l1_struct_0(A_378))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_172, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_226, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_172])).
% 7.74/2.56  tff(c_162, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_230, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_162])).
% 7.74/2.56  tff(c_152, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_228, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_152])).
% 7.74/2.56  tff(c_142, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_231, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_142])).
% 7.74/2.56  tff(c_132, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_225, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_132])).
% 7.74/2.56  tff(c_122, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_229, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_122])).
% 7.74/2.56  tff(c_112, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_227, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_112])).
% 7.74/2.56  tff(c_102, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_232, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_102])).
% 7.74/2.56  tff(c_88, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_186, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_88])).
% 7.74/2.56  tff(c_196, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_186])).
% 7.74/2.56  tff(c_206, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_196])).
% 7.74/2.56  tff(c_250, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_230, c_228, c_231, c_225, c_229, c_227, c_232, c_206])).
% 7.74/2.56  tff(c_58, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_282, plain, (![A_153, B_154, C_155, D_156]: (v1_funct_1(k2_tmap_1(A_153, B_154, C_155, D_156)) | ~l1_struct_0(D_156) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_153), u1_struct_0(B_154)))) | ~v1_funct_2(C_155, u1_struct_0(A_153), u1_struct_0(B_154)) | ~v1_funct_1(C_155) | ~l1_struct_0(B_154) | ~l1_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_288, plain, (![D_156]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_156)) | ~l1_struct_0(D_156) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_282])).
% 7.74/2.56  tff(c_297, plain, (![D_156]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_156)) | ~l1_struct_0(D_156) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_288])).
% 7.74/2.56  tff(c_298, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_297])).
% 7.74/2.56  tff(c_301, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_298])).
% 7.74/2.56  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_301])).
% 7.74/2.56  tff(c_307, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_297])).
% 7.74/2.56  tff(c_306, plain, (![D_156]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_156)) | ~l1_struct_0(D_156))), inference(splitRight, [status(thm)], [c_297])).
% 7.74/2.56  tff(c_308, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_306])).
% 7.74/2.56  tff(c_311, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_308])).
% 7.74/2.56  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_311])).
% 7.74/2.56  tff(c_317, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_306])).
% 7.74/2.56  tff(c_371, plain, (![A_167, B_168, C_169, D_170]: (v1_funct_2(k2_tmap_1(A_167, B_168, C_169, D_170), u1_struct_0(D_170), u1_struct_0(B_168)) | ~l1_struct_0(D_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_167), u1_struct_0(B_168)))) | ~v1_funct_2(C_169, u1_struct_0(A_167), u1_struct_0(B_168)) | ~v1_funct_1(C_169) | ~l1_struct_0(B_168) | ~l1_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_377, plain, (![D_170]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_170), u1_struct_0(D_170), u1_struct_0('#skF_2')) | ~l1_struct_0(D_170) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_371])).
% 7.74/2.56  tff(c_386, plain, (![D_170]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_170), u1_struct_0(D_170), u1_struct_0('#skF_2')) | ~l1_struct_0(D_170))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_317, c_74, c_72, c_377])).
% 7.74/2.56  tff(c_316, plain, (![D_156]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_156)) | ~l1_struct_0(D_156))), inference(splitRight, [status(thm)], [c_306])).
% 7.74/2.56  tff(c_60, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_337])).
% 7.74/2.56  tff(c_265, plain, (![A_150, B_151, C_152]: (m1_pre_topc(k1_tsep_1(A_150, B_151, C_152), A_150) | ~m1_pre_topc(C_152, A_150) | v2_struct_0(C_152) | ~m1_pre_topc(B_151, A_150) | v2_struct_0(B_151) | ~l1_pre_topc(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.74/2.56  tff(c_271, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_60, c_265])).
% 7.74/2.56  tff(c_274, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_66, c_62, c_271])).
% 7.74/2.56  tff(c_275, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_86, c_68, c_64, c_274])).
% 7.74/2.56  tff(c_568, plain, (![C_215, A_214, E_212, D_216, B_213]: (k3_tmap_1(A_214, B_213, C_215, D_216, E_212)=k2_partfun1(u1_struct_0(C_215), u1_struct_0(B_213), E_212, u1_struct_0(D_216)) | ~m1_pre_topc(D_216, C_215) | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_215), u1_struct_0(B_213)))) | ~v1_funct_2(E_212, u1_struct_0(C_215), u1_struct_0(B_213)) | ~v1_funct_1(E_212) | ~m1_pre_topc(D_216, A_214) | ~m1_pre_topc(C_215, A_214) | ~l1_pre_topc(B_213) | ~v2_pre_topc(B_213) | v2_struct_0(B_213) | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214) | v2_struct_0(A_214))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.74/2.56  tff(c_576, plain, (![A_214, D_216]: (k3_tmap_1(A_214, '#skF_2', '#skF_1', D_216, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_216)) | ~m1_pre_topc(D_216, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_216, A_214) | ~m1_pre_topc('#skF_1', A_214) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214) | v2_struct_0(A_214))), inference(resolution, [status(thm)], [c_70, c_568])).
% 7.74/2.56  tff(c_588, plain, (![A_214, D_216]: (k3_tmap_1(A_214, '#skF_2', '#skF_1', D_216, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_216)) | ~m1_pre_topc(D_216, '#skF_1') | ~m1_pre_topc(D_216, A_214) | ~m1_pre_topc('#skF_1', A_214) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214) | v2_struct_0(A_214))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_576])).
% 7.74/2.56  tff(c_591, plain, (![A_219, D_220]: (k3_tmap_1(A_219, '#skF_2', '#skF_1', D_220, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_220)) | ~m1_pre_topc(D_220, '#skF_1') | ~m1_pre_topc(D_220, A_219) | ~m1_pre_topc('#skF_1', A_219) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219))), inference(negUnitSimplification, [status(thm)], [c_80, c_588])).
% 7.74/2.56  tff(c_593, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_275, c_591])).
% 7.74/2.56  tff(c_602, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_275, c_593])).
% 7.74/2.56  tff(c_603, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_86, c_602])).
% 7.74/2.56  tff(c_424, plain, (![A_182, B_183, C_184, D_185]: (k2_partfun1(u1_struct_0(A_182), u1_struct_0(B_183), C_184, u1_struct_0(D_185))=k2_tmap_1(A_182, B_183, C_184, D_185) | ~m1_pre_topc(D_185, A_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_182), u1_struct_0(B_183)))) | ~v1_funct_2(C_184, u1_struct_0(A_182), u1_struct_0(B_183)) | ~v1_funct_1(C_184) | ~l1_pre_topc(B_183) | ~v2_pre_topc(B_183) | v2_struct_0(B_183) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.74/2.56  tff(c_432, plain, (![D_185]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_185))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_185) | ~m1_pre_topc(D_185, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_424])).
% 7.74/2.56  tff(c_444, plain, (![D_185]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_185))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_185) | ~m1_pre_topc(D_185, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_78, c_76, c_74, c_72, c_432])).
% 7.74/2.56  tff(c_445, plain, (![D_185]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_185))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_185) | ~m1_pre_topc(D_185, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_444])).
% 7.74/2.56  tff(c_616, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_603, c_445])).
% 7.74/2.56  tff(c_623, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_616])).
% 7.74/2.56  tff(c_455, plain, (![C_187, B_188, D_189, A_190]: (r2_funct_2(u1_struct_0(C_187), u1_struct_0(B_188), D_189, k3_tmap_1(A_190, B_188, C_187, C_187, D_189)) | ~m1_subset_1(D_189, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_187), u1_struct_0(B_188)))) | ~v1_funct_2(D_189, u1_struct_0(C_187), u1_struct_0(B_188)) | ~v1_funct_1(D_189) | ~m1_pre_topc(C_187, A_190) | v2_struct_0(C_187) | ~l1_pre_topc(B_188) | ~v2_pre_topc(B_188) | v2_struct_0(B_188) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_274])).
% 7.74/2.56  tff(c_463, plain, (![A_190]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_190, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_1', A_190) | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(resolution, [status(thm)], [c_70, c_455])).
% 7.74/2.56  tff(c_475, plain, (![A_190]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_190, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_190) | v2_struct_0('#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_463])).
% 7.74/2.56  tff(c_477, plain, (![A_191]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_191, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(negUnitSimplification, [status(thm)], [c_80, c_86, c_475])).
% 7.74/2.56  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.74/2.56  tff(c_479, plain, (![A_191]: (k3_tmap_1(A_191, '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k3_tmap_1(A_191, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_191, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_191, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_1', A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_477, c_4])).
% 7.74/2.56  tff(c_482, plain, (![A_191]: (k3_tmap_1(A_191, '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k3_tmap_1(A_191, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_191, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_191, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_479])).
% 7.74/2.56  tff(c_645, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_623, c_482])).
% 7.74/2.56  tff(c_652, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_275, c_623, c_623, c_623, c_645])).
% 7.74/2.56  tff(c_653, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_86, c_652])).
% 7.74/2.56  tff(c_734, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_653])).
% 7.74/2.56  tff(c_737, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_316, c_734])).
% 7.74/2.56  tff(c_741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_307, c_737])).
% 7.74/2.56  tff(c_743, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_653])).
% 7.74/2.56  tff(c_20, plain, (![A_58, B_59, C_60, D_61]: (m1_subset_1(k2_tmap_1(A_58, B_59, C_60, D_61), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_61), u1_struct_0(B_59)))) | ~l1_struct_0(D_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58), u1_struct_0(B_59)))) | ~v1_funct_2(C_60, u1_struct_0(A_58), u1_struct_0(B_59)) | ~v1_funct_1(C_60) | ~l1_struct_0(B_59) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.74/2.56  tff(c_742, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_653])).
% 7.74/2.56  tff(c_784, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_742])).
% 7.74/2.56  tff(c_787, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_784])).
% 7.74/2.56  tff(c_791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_307, c_317, c_74, c_72, c_70, c_787])).
% 7.74/2.56  tff(c_793, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_742])).
% 7.74/2.56  tff(c_30, plain, (![A_62, B_63, C_64, D_65]: (v1_funct_1(k2_tmap_1(A_62, B_63, C_64, D_65)) | ~m1_pre_topc(D_65, A_62) | v2_struct_0(D_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_62), u1_struct_0(B_63)))) | ~v5_pre_topc(C_64, A_62, B_63) | ~v1_funct_2(C_64, u1_struct_0(A_62), u1_struct_0(B_63)) | ~v1_funct_1(C_64) | ~l1_pre_topc(B_63) | ~v2_pre_topc(B_63) | v2_struct_0(B_63) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.74/2.56  tff(c_805, plain, (![D_65]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), D_65)) | ~m1_pre_topc(D_65, '#skF_1') | v2_struct_0(D_65) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_793, c_30])).
% 7.74/2.56  tff(c_834, plain, (![D_65]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), D_65)) | ~m1_pre_topc(D_65, '#skF_1') | v2_struct_0(D_65) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_78, c_76, c_743, c_805])).
% 7.74/2.56  tff(c_835, plain, (![D_65]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), D_65)) | ~m1_pre_topc(D_65, '#skF_1') | v2_struct_0(D_65) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_834])).
% 7.74/2.56  tff(c_845, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_835])).
% 7.74/2.56  tff(c_848, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_386, c_845])).
% 7.74/2.56  tff(c_852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_307, c_848])).
% 7.74/2.56  tff(c_854, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_835])).
% 7.74/2.56  tff(c_792, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_742])).
% 7.74/2.56  tff(c_862, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_854, c_792])).
% 7.74/2.56  tff(c_1822, plain, (![E_345, D_343, A_344, B_347, C_346]: (v5_pre_topc(k2_tmap_1(A_344, B_347, E_345, k1_tsep_1(A_344, C_346, D_343)), k1_tsep_1(A_344, C_346, D_343), B_347) | ~m1_subset_1(k2_tmap_1(A_344, B_347, E_345, D_343), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_343), u1_struct_0(B_347)))) | ~v5_pre_topc(k2_tmap_1(A_344, B_347, E_345, D_343), D_343, B_347) | ~v1_funct_2(k2_tmap_1(A_344, B_347, E_345, D_343), u1_struct_0(D_343), u1_struct_0(B_347)) | ~v1_funct_1(k2_tmap_1(A_344, B_347, E_345, D_343)) | ~m1_subset_1(k2_tmap_1(A_344, B_347, E_345, C_346), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346), u1_struct_0(B_347)))) | ~v5_pre_topc(k2_tmap_1(A_344, B_347, E_345, C_346), C_346, B_347) | ~v1_funct_2(k2_tmap_1(A_344, B_347, E_345, C_346), u1_struct_0(C_346), u1_struct_0(B_347)) | ~v1_funct_1(k2_tmap_1(A_344, B_347, E_345, C_346)) | ~m1_subset_1(E_345, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_344), u1_struct_0(B_347)))) | ~v1_funct_2(E_345, u1_struct_0(A_344), u1_struct_0(B_347)) | ~v1_funct_1(E_345) | ~r4_tsep_1(A_344, C_346, D_343) | ~m1_pre_topc(D_343, A_344) | v2_struct_0(D_343) | ~m1_pre_topc(C_346, A_344) | v2_struct_0(C_346) | ~l1_pre_topc(B_347) | ~v2_pre_topc(B_347) | v2_struct_0(B_347) | ~l1_pre_topc(A_344) | ~v2_pre_topc(A_344) | v2_struct_0(A_344))), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.74/2.56  tff(c_1832, plain, (![C_346]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_346, '#skF_5')), k1_tsep_1('#skF_1', C_346, '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346), C_346, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346), u1_struct_0(C_346), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~r4_tsep_1('#skF_1', C_346, '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_346, '#skF_1') | v2_struct_0(C_346) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_232, c_1822])).
% 7.74/2.56  tff(c_1849, plain, (![C_346]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_346, '#skF_5')), k1_tsep_1('#skF_1', C_346, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346), C_346, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346), u1_struct_0(C_346), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346)) | ~r4_tsep_1('#skF_1', C_346, '#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_346, '#skF_1') | v2_struct_0(C_346) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_78, c_76, c_62, c_74, c_72, c_70, c_225, c_229, c_227, c_1832])).
% 7.74/2.56  tff(c_1857, plain, (![C_348]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_348, '#skF_5')), k1_tsep_1('#skF_1', C_348, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_348), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_348), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_348), C_348, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_348), u1_struct_0(C_348), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_348)) | ~r4_tsep_1('#skF_1', C_348, '#skF_5') | ~m1_pre_topc(C_348, '#skF_1') | v2_struct_0(C_348))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_64, c_1849])).
% 7.74/2.56  tff(c_1878, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_231, c_1857])).
% 7.74/2.56  tff(c_1899, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_58, c_226, c_230, c_228, c_862, c_60, c_60, c_1878])).
% 7.74/2.56  tff(c_1901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_250, c_1899])).
% 7.74/2.56  tff(c_1903, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_102])).
% 7.74/2.56  tff(c_2031, plain, (~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2022, c_1903])).
% 7.74/2.56  tff(c_2037, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1973, c_1996, c_74, c_72, c_70, c_2031])).
% 7.74/2.56  tff(c_2040, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6, c_2037])).
% 7.74/2.56  tff(c_2044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_224, c_2040])).
% 7.74/2.56  tff(c_2046, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_142])).
% 7.74/2.56  tff(c_2144, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2135, c_2046])).
% 7.74/2.56  tff(c_2150, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2107, c_2117, c_74, c_72, c_70, c_2144])).
% 7.74/2.56  tff(c_2153, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_2150])).
% 7.74/2.56  tff(c_2157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_2153])).
% 7.74/2.56  tff(c_2159, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_162])).
% 7.74/2.56  tff(c_2250, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_2246, c_2159])).
% 7.74/2.56  tff(c_2263, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_2250])).
% 7.74/2.56  tff(c_2267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_2263])).
% 7.74/2.56  tff(c_2269, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_122])).
% 7.74/2.56  tff(c_2363, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2359, c_2269])).
% 7.74/2.56  tff(c_2366, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6, c_2363])).
% 7.74/2.56  tff(c_2370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_224, c_2366])).
% 7.74/2.56  tff(c_2371, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_152])).
% 7.74/2.56  tff(c_2504, plain, (![A_520, B_521, C_522, D_523]: (v5_pre_topc(k2_tmap_1(A_520, B_521, C_522, D_523), D_523, B_521) | ~m1_pre_topc(D_523, A_520) | v2_struct_0(D_523) | ~m1_subset_1(C_522, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_520), u1_struct_0(B_521)))) | ~v5_pre_topc(C_522, A_520, B_521) | ~v1_funct_2(C_522, u1_struct_0(A_520), u1_struct_0(B_521)) | ~v1_funct_1(C_522) | ~l1_pre_topc(B_521) | ~v2_pre_topc(B_521) | v2_struct_0(B_521) | ~l1_pre_topc(A_520) | ~v2_pre_topc(A_520) | v2_struct_0(A_520))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.74/2.56  tff(c_2508, plain, (![D_523]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_523), D_523, '#skF_2') | ~m1_pre_topc(D_523, '#skF_1') | v2_struct_0(D_523) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_2504])).
% 7.74/2.56  tff(c_2512, plain, (![D_523]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_523), D_523, '#skF_2') | ~m1_pre_topc(D_523, '#skF_1') | v2_struct_0(D_523) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_78, c_76, c_74, c_72, c_2371, c_2508])).
% 7.74/2.56  tff(c_2524, plain, (![D_528]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_528), D_528, '#skF_2') | ~m1_pre_topc(D_528, '#skF_1') | v2_struct_0(D_528))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_2512])).
% 7.74/2.56  tff(c_2372, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_152])).
% 7.74/2.56  tff(c_2527, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_2524, c_2372])).
% 7.74/2.56  tff(c_2530, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2527])).
% 7.74/2.56  tff(c_2532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2530])).
% 7.74/2.56  tff(c_2533, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_112])).
% 7.74/2.56  tff(c_2690, plain, (![A_581, B_582, C_583, D_584]: (v5_pre_topc(k2_tmap_1(A_581, B_582, C_583, D_584), D_584, B_582) | ~m1_pre_topc(D_584, A_581) | v2_struct_0(D_584) | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_581), u1_struct_0(B_582)))) | ~v5_pre_topc(C_583, A_581, B_582) | ~v1_funct_2(C_583, u1_struct_0(A_581), u1_struct_0(B_582)) | ~v1_funct_1(C_583) | ~l1_pre_topc(B_582) | ~v2_pre_topc(B_582) | v2_struct_0(B_582) | ~l1_pre_topc(A_581) | ~v2_pre_topc(A_581) | v2_struct_0(A_581))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.74/2.56  tff(c_2694, plain, (![D_584]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_584), D_584, '#skF_2') | ~m1_pre_topc(D_584, '#skF_1') | v2_struct_0(D_584) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_2690])).
% 7.74/2.56  tff(c_2698, plain, (![D_584]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_584), D_584, '#skF_2') | ~m1_pre_topc(D_584, '#skF_1') | v2_struct_0(D_584) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_78, c_76, c_74, c_72, c_2533, c_2694])).
% 7.74/2.56  tff(c_2700, plain, (![D_585]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_585), D_585, '#skF_2') | ~m1_pre_topc(D_585, '#skF_1') | v2_struct_0(D_585))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_2698])).
% 7.74/2.56  tff(c_2534, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_112])).
% 7.74/2.56  tff(c_2703, plain, (~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2700, c_2534])).
% 7.74/2.56  tff(c_2706, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2703])).
% 7.74/2.56  tff(c_2708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2706])).
% 7.74/2.56  tff(c_2710, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_172])).
% 7.74/2.56  tff(c_2800, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_2796, c_2710])).
% 7.74/2.56  tff(c_2803, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_2800])).
% 7.74/2.56  tff(c_2807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_2803])).
% 7.74/2.56  tff(c_2809, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_132])).
% 7.74/2.56  tff(c_2898, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2894, c_2809])).
% 7.74/2.56  tff(c_2901, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6, c_2898])).
% 7.74/2.56  tff(c_2905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_224, c_2901])).
% 7.74/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.56  
% 7.74/2.56  Inference rules
% 7.74/2.56  ----------------------
% 7.74/2.56  #Ref     : 0
% 7.74/2.56  #Sup     : 459
% 7.74/2.56  #Fact    : 0
% 7.74/2.56  #Define  : 0
% 7.74/2.56  #Split   : 39
% 7.74/2.56  #Chain   : 0
% 7.74/2.56  #Close   : 0
% 7.74/2.56  
% 7.74/2.56  Ordering : KBO
% 7.74/2.56  
% 7.74/2.56  Simplification rules
% 7.74/2.56  ----------------------
% 7.74/2.56  #Subsume      : 130
% 7.74/2.56  #Demod        : 1580
% 7.74/2.56  #Tautology    : 169
% 7.74/2.56  #SimpNegUnit  : 165
% 7.74/2.56  #BackRed      : 10
% 7.74/2.56  
% 7.74/2.56  #Partial instantiations: 0
% 7.74/2.56  #Strategies tried      : 1
% 7.74/2.56  
% 7.74/2.56  Timing (in seconds)
% 7.74/2.56  ----------------------
% 7.74/2.56  Preprocessing        : 0.47
% 7.74/2.56  Parsing              : 0.23
% 7.74/2.56  CNF conversion       : 0.07
% 7.74/2.56  Main loop            : 1.20
% 7.74/2.56  Inferencing          : 0.40
% 7.74/2.56  Reduction            : 0.41
% 7.74/2.56  Demodulation         : 0.31
% 7.74/2.56  BG Simplification    : 0.07
% 7.74/2.56  Subsumption          : 0.27
% 7.74/2.56  Abstraction          : 0.05
% 7.74/2.56  MUC search           : 0.00
% 7.74/2.56  Cooper               : 0.00
% 7.74/2.56  Total                : 1.75
% 7.74/2.56  Index Insertion      : 0.00
% 7.74/2.56  Index Deletion       : 0.00
% 7.74/2.56  Index Matching       : 0.00
% 7.74/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
