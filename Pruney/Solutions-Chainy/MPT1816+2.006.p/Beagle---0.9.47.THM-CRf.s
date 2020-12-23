%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:07 EST 2020

% Result     : Theorem 8.79s
% Output     : CNFRefutation 9.30s
% Verified   : 
% Statistics : Number of formulae       :  318 (2902 expanded)
%              Number of leaves         :   41 (1114 expanded)
%              Depth                    :   21
%              Number of atoms          : 1190 (28216 expanded)
%              Number of equality atoms :   53 (1227 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_253,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_130,axiom,(
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

tff(f_112,axiom,(
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

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_90,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_190,axiom,(
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

tff(c_80,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_211,plain,(
    ! [B_101,A_102] :
      ( l1_pre_topc(B_101)
      | ~ m1_pre_topc(B_101,A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_214,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_211])).

tff(c_220,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_214])).

tff(c_14,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_70,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_6029,plain,(
    ! [A_861,B_862,C_863,D_864] :
      ( v1_funct_1(k2_tmap_1(A_861,B_862,C_863,D_864))
      | ~ l1_struct_0(D_864)
      | ~ m1_subset_1(C_863,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_861),u1_struct_0(B_862))))
      | ~ v1_funct_2(C_863,u1_struct_0(A_861),u1_struct_0(B_862))
      | ~ v1_funct_1(C_863)
      | ~ l1_struct_0(B_862)
      | ~ l1_struct_0(A_861) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6031,plain,(
    ! [D_864] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_864))
      | ~ l1_struct_0(D_864)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_6029])).

tff(c_6034,plain,(
    ! [D_864] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_864))
      | ~ l1_struct_0(D_864)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_6031])).

tff(c_6035,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6034])).

tff(c_6044,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_6035])).

tff(c_6048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6044])).

tff(c_6049,plain,(
    ! [D_864] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_864))
      | ~ l1_struct_0(D_864) ) ),
    inference(splitRight,[status(thm)],[c_6034])).

tff(c_6051,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6049])).

tff(c_6054,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_6051])).

tff(c_6058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6054])).

tff(c_6061,plain,(
    ! [D_869] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_869))
      | ~ l1_struct_0(D_869) ) ),
    inference(splitRight,[status(thm)],[c_6049])).

tff(c_60,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_217,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_211])).

tff(c_223,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_217])).

tff(c_5921,plain,(
    ! [A_839,B_840,C_841,D_842] :
      ( v1_funct_1(k2_tmap_1(A_839,B_840,C_841,D_842))
      | ~ l1_struct_0(D_842)
      | ~ m1_subset_1(C_841,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_839),u1_struct_0(B_840))))
      | ~ v1_funct_2(C_841,u1_struct_0(A_839),u1_struct_0(B_840))
      | ~ v1_funct_1(C_841)
      | ~ l1_struct_0(B_840)
      | ~ l1_struct_0(A_839) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5923,plain,(
    ! [D_842] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_842))
      | ~ l1_struct_0(D_842)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_5921])).

tff(c_5926,plain,(
    ! [D_842] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_842))
      | ~ l1_struct_0(D_842)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_5923])).

tff(c_5933,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5926])).

tff(c_5936,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_5933])).

tff(c_5940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5936])).

tff(c_5941,plain,(
    ! [D_842] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_842))
      | ~ l1_struct_0(D_842) ) ),
    inference(splitRight,[status(thm)],[c_5926])).

tff(c_5943,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5941])).

tff(c_5946,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_5943])).

tff(c_5950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5946])).

tff(c_5953,plain,(
    ! [D_843] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_843))
      | ~ l1_struct_0(D_843) ) ),
    inference(splitRight,[status(thm)],[c_5941])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_4193,plain,(
    ! [A_509,B_510,C_511,D_512] :
      ( v1_funct_1(k2_tmap_1(A_509,B_510,C_511,D_512))
      | ~ l1_struct_0(D_512)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_509),u1_struct_0(B_510))))
      | ~ v1_funct_2(C_511,u1_struct_0(A_509),u1_struct_0(B_510))
      | ~ v1_funct_1(C_511)
      | ~ l1_struct_0(B_510)
      | ~ l1_struct_0(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4195,plain,(
    ! [D_512] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_512))
      | ~ l1_struct_0(D_512)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_4193])).

tff(c_4198,plain,(
    ! [D_512] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_512))
      | ~ l1_struct_0(D_512)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4195])).

tff(c_4199,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4198])).

tff(c_4202,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_4199])).

tff(c_4206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4202])).

tff(c_4208,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4198])).

tff(c_4207,plain,(
    ! [D_512] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_512))
      | ~ l1_struct_0(D_512) ) ),
    inference(splitRight,[status(thm)],[c_4198])).

tff(c_4209,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4207])).

tff(c_4212,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_4209])).

tff(c_4216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4212])).

tff(c_4218,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4207])).

tff(c_4227,plain,(
    ! [A_517,B_518,C_519,D_520] :
      ( v1_funct_2(k2_tmap_1(A_517,B_518,C_519,D_520),u1_struct_0(D_520),u1_struct_0(B_518))
      | ~ l1_struct_0(D_520)
      | ~ m1_subset_1(C_519,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_517),u1_struct_0(B_518))))
      | ~ v1_funct_2(C_519,u1_struct_0(A_517),u1_struct_0(B_518))
      | ~ v1_funct_1(C_519)
      | ~ l1_struct_0(B_518)
      | ~ l1_struct_0(A_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4229,plain,(
    ! [D_520] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_520),u1_struct_0(D_520),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_520)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_4227])).

tff(c_4257,plain,(
    ! [D_525] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_525),u1_struct_0(D_525),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_525) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4208,c_4218,c_72,c_70,c_4229])).

tff(c_4089,plain,(
    ! [A_481,B_482,C_483,D_484] :
      ( v1_funct_1(k2_tmap_1(A_481,B_482,C_483,D_484))
      | ~ l1_struct_0(D_484)
      | ~ m1_subset_1(C_483,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_481),u1_struct_0(B_482))))
      | ~ v1_funct_2(C_483,u1_struct_0(A_481),u1_struct_0(B_482))
      | ~ v1_funct_1(C_483)
      | ~ l1_struct_0(B_482)
      | ~ l1_struct_0(A_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4091,plain,(
    ! [D_484] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_484))
      | ~ l1_struct_0(D_484)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_4089])).

tff(c_4094,plain,(
    ! [D_484] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_484))
      | ~ l1_struct_0(D_484)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4091])).

tff(c_4095,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4094])).

tff(c_4098,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_4095])).

tff(c_4102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4098])).

tff(c_4104,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4094])).

tff(c_4103,plain,(
    ! [D_484] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_484))
      | ~ l1_struct_0(D_484) ) ),
    inference(splitRight,[status(thm)],[c_4094])).

tff(c_4105,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4103])).

tff(c_4114,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_4105])).

tff(c_4118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4114])).

tff(c_4120,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4103])).

tff(c_4122,plain,(
    ! [A_490,B_491,C_492,D_493] :
      ( v1_funct_2(k2_tmap_1(A_490,B_491,C_492,D_493),u1_struct_0(D_493),u1_struct_0(B_491))
      | ~ l1_struct_0(D_493)
      | ~ m1_subset_1(C_492,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_490),u1_struct_0(B_491))))
      | ~ v1_funct_2(C_492,u1_struct_0(A_490),u1_struct_0(B_491))
      | ~ v1_funct_1(C_492)
      | ~ l1_struct_0(B_491)
      | ~ l1_struct_0(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4124,plain,(
    ! [D_493] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_493),u1_struct_0(D_493),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_493)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_4122])).

tff(c_4128,plain,(
    ! [D_494] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_494),u1_struct_0(D_494),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_494) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4104,c_4120,c_72,c_70,c_4124])).

tff(c_3945,plain,(
    ! [A_446,B_447,C_448,D_449] :
      ( v1_funct_1(k2_tmap_1(A_446,B_447,C_448,D_449))
      | ~ l1_struct_0(D_449)
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_446),u1_struct_0(B_447))))
      | ~ v1_funct_2(C_448,u1_struct_0(A_446),u1_struct_0(B_447))
      | ~ v1_funct_1(C_448)
      | ~ l1_struct_0(B_447)
      | ~ l1_struct_0(A_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3947,plain,(
    ! [D_449] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_449))
      | ~ l1_struct_0(D_449)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_3945])).

tff(c_3950,plain,(
    ! [D_449] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_449))
      | ~ l1_struct_0(D_449)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_3947])).

tff(c_3957,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3950])).

tff(c_3960,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_3957])).

tff(c_3964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3960])).

tff(c_3966,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3950])).

tff(c_3951,plain,(
    ! [A_450,B_451,C_452,D_453] :
      ( v1_funct_2(k2_tmap_1(A_450,B_451,C_452,D_453),u1_struct_0(D_453),u1_struct_0(B_451))
      | ~ l1_struct_0(D_453)
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_450),u1_struct_0(B_451))))
      | ~ v1_funct_2(C_452,u1_struct_0(A_450),u1_struct_0(B_451))
      | ~ v1_funct_1(C_452)
      | ~ l1_struct_0(B_451)
      | ~ l1_struct_0(A_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3953,plain,(
    ! [D_453] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_453),u1_struct_0(D_453),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_453)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_3951])).

tff(c_3956,plain,(
    ! [D_453] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_453),u1_struct_0(D_453),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_453)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_3953])).

tff(c_3968,plain,(
    ! [D_453] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_453),u1_struct_0(D_453),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_453)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3966,c_3956])).

tff(c_3969,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3968])).

tff(c_3972,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_3969])).

tff(c_3976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3972])).

tff(c_3978,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3968])).

tff(c_3983,plain,(
    ! [A_456,B_457,C_458,D_459] :
      ( m1_subset_1(k2_tmap_1(A_456,B_457,C_458,D_459),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_459),u1_struct_0(B_457))))
      | ~ l1_struct_0(D_459)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_456),u1_struct_0(B_457))))
      | ~ v1_funct_2(C_458,u1_struct_0(A_456),u1_struct_0(B_457))
      | ~ v1_funct_1(C_458)
      | ~ l1_struct_0(B_457)
      | ~ l1_struct_0(A_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3780,plain,(
    ! [A_409,B_410,C_411,D_412] :
      ( v1_funct_1(k2_tmap_1(A_409,B_410,C_411,D_412))
      | ~ l1_struct_0(D_412)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_409),u1_struct_0(B_410))))
      | ~ v1_funct_2(C_411,u1_struct_0(A_409),u1_struct_0(B_410))
      | ~ v1_funct_1(C_411)
      | ~ l1_struct_0(B_410)
      | ~ l1_struct_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3784,plain,(
    ! [D_412] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_412))
      | ~ l1_struct_0(D_412)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_3780])).

tff(c_3790,plain,(
    ! [D_412] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_412))
      | ~ l1_struct_0(D_412)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_3784])).

tff(c_3791,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3790])).

tff(c_3805,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_3791])).

tff(c_3809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3805])).

tff(c_3811,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3790])).

tff(c_3810,plain,(
    ! [D_412] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_412))
      | ~ l1_struct_0(D_412) ) ),
    inference(splitRight,[status(thm)],[c_3790])).

tff(c_3812,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3810])).

tff(c_3816,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_3812])).

tff(c_3820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3816])).

tff(c_3822,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3810])).

tff(c_3852,plain,(
    ! [A_425,B_426,C_427,D_428] :
      ( m1_subset_1(k2_tmap_1(A_425,B_426,C_427,D_428),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_428),u1_struct_0(B_426))))
      | ~ l1_struct_0(D_428)
      | ~ m1_subset_1(C_427,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_425),u1_struct_0(B_426))))
      | ~ v1_funct_2(C_427,u1_struct_0(A_425),u1_struct_0(B_426))
      | ~ v1_funct_1(C_427)
      | ~ l1_struct_0(B_426)
      | ~ l1_struct_0(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_170,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_252,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_160,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_257,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_150,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_255,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_140,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_258,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_130,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_253,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_120,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_256,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_110,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_254,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_100,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_279,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_100])).

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
    inference(cnfTransformation,[status(thm)],[f_253])).

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

tff(c_366,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_257,c_255,c_258,c_253,c_256,c_254,c_279,c_204])).

tff(c_56,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_58,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_367,plain,(
    ! [A_126,B_127,C_128] :
      ( m1_pre_topc(k1_tsep_1(A_126,B_127,C_128),A_126)
      | ~ m1_pre_topc(C_128,A_126)
      | v2_struct_0(C_128)
      | ~ m1_pre_topc(B_127,A_126)
      | v2_struct_0(B_127)
      | ~ l1_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_373,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_367])).

tff(c_376,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_64,c_60,c_373])).

tff(c_377,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_66,c_62,c_376])).

tff(c_82,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_308,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k2_partfun1(A_113,B_114,C_115,D_116) = k7_relat_1(C_115,D_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_314,plain,(
    ! [D_116] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_116) = k7_relat_1('#skF_3',D_116)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_68,c_308])).

tff(c_323,plain,(
    ! [D_116] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_116) = k7_relat_1('#skF_3',D_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_314])).

tff(c_581,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( k2_partfun1(u1_struct_0(A_172),u1_struct_0(B_173),C_174,u1_struct_0(D_175)) = k2_tmap_1(A_172,B_173,C_174,D_175)
      | ~ m1_pre_topc(D_175,A_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172),u1_struct_0(B_173))))
      | ~ v1_funct_2(C_174,u1_struct_0(A_172),u1_struct_0(B_173))
      | ~ v1_funct_1(C_174)
      | ~ l1_pre_topc(B_173)
      | ~ v2_pre_topc(B_173)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_589,plain,(
    ! [D_175] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_175)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_175)
      | ~ m1_pre_topc(D_175,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_581])).

tff(c_601,plain,(
    ! [D_175] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_175)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_175)
      | ~ m1_pre_topc(D_175,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_72,c_70,c_323,c_589])).

tff(c_608,plain,(
    ! [D_177] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_177)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_177)
      | ~ m1_pre_topc(D_177,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_601])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_224,plain,(
    ! [B_103,A_104] :
      ( v1_relat_1(B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_104))
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_227,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_68,c_224])).

tff(c_230,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_227])).

tff(c_231,plain,(
    ! [C_105,A_106,B_107] :
      ( v4_relat_1(C_105,A_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_235,plain,(
    v4_relat_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_231])).

tff(c_236,plain,(
    ! [B_108,A_109] :
      ( k7_relat_1(B_108,A_109) = B_108
      | ~ v4_relat_1(B_108,A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_239,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_236])).

tff(c_242,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_239])).

tff(c_614,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_242])).

tff(c_623,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_614])).

tff(c_2880,plain,(
    ! [D_361,C_360,A_357,E_358,B_359] :
      ( v5_pre_topc(k2_tmap_1(A_357,B_359,E_358,k1_tsep_1(A_357,C_360,D_361)),k1_tsep_1(A_357,C_360,D_361),B_359)
      | ~ m1_subset_1(k2_tmap_1(A_357,B_359,E_358,D_361),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_361),u1_struct_0(B_359))))
      | ~ v5_pre_topc(k2_tmap_1(A_357,B_359,E_358,D_361),D_361,B_359)
      | ~ v1_funct_2(k2_tmap_1(A_357,B_359,E_358,D_361),u1_struct_0(D_361),u1_struct_0(B_359))
      | ~ v1_funct_1(k2_tmap_1(A_357,B_359,E_358,D_361))
      | ~ m1_subset_1(k2_tmap_1(A_357,B_359,E_358,C_360),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360),u1_struct_0(B_359))))
      | ~ v5_pre_topc(k2_tmap_1(A_357,B_359,E_358,C_360),C_360,B_359)
      | ~ v1_funct_2(k2_tmap_1(A_357,B_359,E_358,C_360),u1_struct_0(C_360),u1_struct_0(B_359))
      | ~ v1_funct_1(k2_tmap_1(A_357,B_359,E_358,C_360))
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_357),u1_struct_0(B_359))))
      | ~ v1_funct_2(E_358,u1_struct_0(A_357),u1_struct_0(B_359))
      | ~ v1_funct_1(E_358)
      | ~ r4_tsep_1(A_357,C_360,D_361)
      | ~ m1_pre_topc(D_361,A_357)
      | v2_struct_0(D_361)
      | ~ m1_pre_topc(C_360,A_357)
      | v2_struct_0(C_360)
      | ~ l1_pre_topc(B_359)
      | ~ v2_pre_topc(B_359)
      | v2_struct_0(B_359)
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357)
      | v2_struct_0(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_2892,plain,(
    ! [C_360] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_360,'#skF_5')),k1_tsep_1('#skF_1',C_360,'#skF_5'),'#skF_2')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360),C_360,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360),u1_struct_0(C_360),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ r4_tsep_1('#skF_1',C_360,'#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_360,'#skF_1')
      | v2_struct_0(C_360)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_279,c_2880])).

tff(c_2910,plain,(
    ! [C_360] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_360,'#skF_5')),k1_tsep_1('#skF_1',C_360,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360),C_360,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360),u1_struct_0(C_360),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360))
      | ~ r4_tsep_1('#skF_1',C_360,'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_360,'#skF_1')
      | v2_struct_0(C_360)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_60,c_72,c_70,c_68,c_253,c_256,c_254,c_2892])).

tff(c_3668,plain,(
    ! [C_390] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_390,'#skF_5')),k1_tsep_1('#skF_1',C_390,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_390),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_390),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_390),C_390,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_390),u1_struct_0(C_390),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_390))
      | ~ r4_tsep_1('#skF_1',C_390,'#skF_5')
      | ~ m1_pre_topc(C_390,'#skF_1')
      | v2_struct_0(C_390) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_62,c_2910])).

tff(c_3685,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_258,c_3668])).

tff(c_3702,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_56,c_252,c_257,c_255,c_623,c_58,c_58,c_3685])).

tff(c_3704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_366,c_3702])).

tff(c_3706,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_3861,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3852,c_3706])).

tff(c_3876,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3811,c_3822,c_72,c_70,c_68,c_3861])).

tff(c_3884,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_3876])).

tff(c_3888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_3884])).

tff(c_3890,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_3992,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3983,c_3890])).

tff(c_4007,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3966,c_3978,c_72,c_70,c_68,c_3992])).

tff(c_4025,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_4007])).

tff(c_4029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_4025])).

tff(c_4031,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_4132,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4128,c_4031])).

tff(c_4135,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_4132])).

tff(c_4139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_4135])).

tff(c_4141,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_4261,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4257,c_4141])).

tff(c_4264,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_4261])).

tff(c_4268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_4264])).

tff(c_4270,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_4306,plain,(
    ! [A_537,B_538,C_539] :
      ( m1_pre_topc(k1_tsep_1(A_537,B_538,C_539),A_537)
      | ~ m1_pre_topc(C_539,A_537)
      | v2_struct_0(C_539)
      | ~ m1_pre_topc(B_538,A_537)
      | v2_struct_0(B_538)
      | ~ l1_pre_topc(A_537)
      | v2_struct_0(A_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4312,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_4306])).

tff(c_4315,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_64,c_60,c_4312])).

tff(c_4316,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_66,c_62,c_4315])).

tff(c_4274,plain,(
    ! [A_526,B_527,C_528,D_529] :
      ( k2_partfun1(A_526,B_527,C_528,D_529) = k7_relat_1(C_528,D_529)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(k2_zfmisc_1(A_526,B_527)))
      | ~ v1_funct_1(C_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4276,plain,(
    ! [D_529] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_529) = k7_relat_1('#skF_3',D_529)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_68,c_4274])).

tff(c_4279,plain,(
    ! [D_529] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_529) = k7_relat_1('#skF_3',D_529) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4276])).

tff(c_4394,plain,(
    ! [A_561,B_562,C_563,D_564] :
      ( k2_partfun1(u1_struct_0(A_561),u1_struct_0(B_562),C_563,u1_struct_0(D_564)) = k2_tmap_1(A_561,B_562,C_563,D_564)
      | ~ m1_pre_topc(D_564,A_561)
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_561),u1_struct_0(B_562))))
      | ~ v1_funct_2(C_563,u1_struct_0(A_561),u1_struct_0(B_562))
      | ~ v1_funct_1(C_563)
      | ~ l1_pre_topc(B_562)
      | ~ v2_pre_topc(B_562)
      | v2_struct_0(B_562)
      | ~ l1_pre_topc(A_561)
      | ~ v2_pre_topc(A_561)
      | v2_struct_0(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4398,plain,(
    ! [D_564] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_564)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_564)
      | ~ m1_pre_topc(D_564,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_4394])).

tff(c_4402,plain,(
    ! [D_564] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_564)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_564)
      | ~ m1_pre_topc(D_564,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_72,c_70,c_4279,c_4398])).

tff(c_4404,plain,(
    ! [D_565] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_565)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_565)
      | ~ m1_pre_topc(D_565,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_4402])).

tff(c_4410,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4404,c_242])).

tff(c_4419,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4316,c_4410])).

tff(c_4269,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_4749,plain,(
    ! [B_649,E_648,D_651,A_647,C_650] :
      ( v5_pre_topc(k2_tmap_1(A_647,B_649,E_648,C_650),C_650,B_649)
      | ~ m1_subset_1(k2_tmap_1(A_647,B_649,E_648,k1_tsep_1(A_647,C_650,D_651)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_647,C_650,D_651)),u1_struct_0(B_649))))
      | ~ v5_pre_topc(k2_tmap_1(A_647,B_649,E_648,k1_tsep_1(A_647,C_650,D_651)),k1_tsep_1(A_647,C_650,D_651),B_649)
      | ~ v1_funct_2(k2_tmap_1(A_647,B_649,E_648,k1_tsep_1(A_647,C_650,D_651)),u1_struct_0(k1_tsep_1(A_647,C_650,D_651)),u1_struct_0(B_649))
      | ~ v1_funct_1(k2_tmap_1(A_647,B_649,E_648,k1_tsep_1(A_647,C_650,D_651)))
      | ~ m1_subset_1(E_648,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_647),u1_struct_0(B_649))))
      | ~ v1_funct_2(E_648,u1_struct_0(A_647),u1_struct_0(B_649))
      | ~ v1_funct_1(E_648)
      | ~ r4_tsep_1(A_647,C_650,D_651)
      | ~ m1_pre_topc(D_651,A_647)
      | v2_struct_0(D_651)
      | ~ m1_pre_topc(C_650,A_647)
      | v2_struct_0(C_650)
      | ~ l1_pre_topc(B_649)
      | ~ v2_pre_topc(B_649)
      | v2_struct_0(B_649)
      | ~ l1_pre_topc(A_647)
      | ~ v2_pre_topc(A_647)
      | v2_struct_0(A_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_4759,plain,(
    ! [B_649,E_648] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_649,E_648,'#skF_4'),'#skF_4',B_649)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_649,E_648,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_649))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_649,E_648,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_649)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_649,E_648,k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_649))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_649,E_648,k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_648,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_649))))
      | ~ v1_funct_2(E_648,u1_struct_0('#skF_1'),u1_struct_0(B_649))
      | ~ v1_funct_1(E_648)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_649)
      | ~ v2_pre_topc(B_649)
      | v2_struct_0(B_649)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_4749])).

tff(c_4765,plain,(
    ! [B_649,E_648] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_649,E_648,'#skF_4'),'#skF_4',B_649)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_649,E_648,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_649))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_649,E_648,'#skF_1'),'#skF_1',B_649)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_649,E_648,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_649))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_649,E_648,'#skF_1'))
      | ~ m1_subset_1(E_648,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_649))))
      | ~ v1_funct_2(E_648,u1_struct_0('#skF_1'),u1_struct_0(B_649))
      | ~ v1_funct_1(E_648)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_649)
      | ~ v2_pre_topc(B_649)
      | v2_struct_0(B_649)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_64,c_60,c_56,c_58,c_58,c_58,c_58,c_58,c_58,c_4759])).

tff(c_4800,plain,(
    ! [B_656,E_657] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_656,E_657,'#skF_4'),'#skF_4',B_656)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_656,E_657,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_656))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_656,E_657,'#skF_1'),'#skF_1',B_656)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_656,E_657,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_656))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_656,E_657,'#skF_1'))
      | ~ m1_subset_1(E_657,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_656))))
      | ~ v1_funct_2(E_657,u1_struct_0('#skF_1'),u1_struct_0(B_656))
      | ~ v1_funct_1(E_657)
      | ~ l1_pre_topc(B_656)
      | ~ v2_pre_topc(B_656)
      | v2_struct_0(B_656) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_66,c_62,c_4765])).

tff(c_4803,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4419,c_4800])).

tff(c_4809,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_72,c_4419,c_70,c_4419,c_4269,c_4419,c_68,c_4803])).

tff(c_4811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4270,c_4809])).

tff(c_4813,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_4859,plain,(
    ! [A_672,B_673,C_674,D_675] :
      ( v1_funct_1(k2_tmap_1(A_672,B_673,C_674,D_675))
      | ~ l1_struct_0(D_675)
      | ~ m1_subset_1(C_674,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_672),u1_struct_0(B_673))))
      | ~ v1_funct_2(C_674,u1_struct_0(A_672),u1_struct_0(B_673))
      | ~ v1_funct_1(C_674)
      | ~ l1_struct_0(B_673)
      | ~ l1_struct_0(A_672) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4861,plain,(
    ! [D_675] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_675))
      | ~ l1_struct_0(D_675)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_4859])).

tff(c_4864,plain,(
    ! [D_675] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_675))
      | ~ l1_struct_0(D_675)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4861])).

tff(c_4871,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4864])).

tff(c_4874,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_4871])).

tff(c_4878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4874])).

tff(c_4880,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4864])).

tff(c_4848,plain,(
    ! [A_669,B_670,C_671] :
      ( m1_pre_topc(k1_tsep_1(A_669,B_670,C_671),A_669)
      | ~ m1_pre_topc(C_671,A_669)
      | v2_struct_0(C_671)
      | ~ m1_pre_topc(B_670,A_669)
      | v2_struct_0(B_670)
      | ~ l1_pre_topc(A_669)
      | v2_struct_0(A_669) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4854,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_4848])).

tff(c_4857,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_64,c_60,c_4854])).

tff(c_4858,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_66,c_62,c_4857])).

tff(c_4818,plain,(
    ! [A_658,B_659,C_660,D_661] :
      ( k2_partfun1(A_658,B_659,C_660,D_661) = k7_relat_1(C_660,D_661)
      | ~ m1_subset_1(C_660,k1_zfmisc_1(k2_zfmisc_1(A_658,B_659)))
      | ~ v1_funct_1(C_660) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4820,plain,(
    ! [D_661] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_661) = k7_relat_1('#skF_3',D_661)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_68,c_4818])).

tff(c_4823,plain,(
    ! [D_661] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_661) = k7_relat_1('#skF_3',D_661) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4820])).

tff(c_4973,plain,(
    ! [A_705,B_706,C_707,D_708] :
      ( k2_partfun1(u1_struct_0(A_705),u1_struct_0(B_706),C_707,u1_struct_0(D_708)) = k2_tmap_1(A_705,B_706,C_707,D_708)
      | ~ m1_pre_topc(D_708,A_705)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_705),u1_struct_0(B_706))))
      | ~ v1_funct_2(C_707,u1_struct_0(A_705),u1_struct_0(B_706))
      | ~ v1_funct_1(C_707)
      | ~ l1_pre_topc(B_706)
      | ~ v2_pre_topc(B_706)
      | v2_struct_0(B_706)
      | ~ l1_pre_topc(A_705)
      | ~ v2_pre_topc(A_705)
      | v2_struct_0(A_705) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4977,plain,(
    ! [D_708] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_708)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_708)
      | ~ m1_pre_topc(D_708,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_4973])).

tff(c_4981,plain,(
    ! [D_708] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_708)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_708)
      | ~ m1_pre_topc(D_708,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_72,c_70,c_4823,c_4977])).

tff(c_4983,plain,(
    ! [D_709] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_709)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_709)
      | ~ m1_pre_topc(D_709,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_4981])).

tff(c_4989,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4983,c_242])).

tff(c_4998,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4858,c_4989])).

tff(c_4812,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_4879,plain,(
    ! [D_675] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_675))
      | ~ l1_struct_0(D_675) ) ),
    inference(splitRight,[status(thm)],[c_4864])).

tff(c_4881,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4879])).

tff(c_4884,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_4881])).

tff(c_4888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4884])).

tff(c_4889,plain,(
    ! [D_675] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_675))
      | ~ l1_struct_0(D_675) ) ),
    inference(splitRight,[status(thm)],[c_4879])).

tff(c_4890,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4879])).

tff(c_4899,plain,(
    ! [A_680,B_681,C_682,D_683] :
      ( v1_funct_2(k2_tmap_1(A_680,B_681,C_682,D_683),u1_struct_0(D_683),u1_struct_0(B_681))
      | ~ l1_struct_0(D_683)
      | ~ m1_subset_1(C_682,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_680),u1_struct_0(B_681))))
      | ~ v1_funct_2(C_682,u1_struct_0(A_680),u1_struct_0(B_681))
      | ~ v1_funct_1(C_682)
      | ~ l1_struct_0(B_681)
      | ~ l1_struct_0(A_680) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4901,plain,(
    ! [D_683] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683),u1_struct_0(D_683),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_683)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_4899])).

tff(c_4904,plain,(
    ! [D_683] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683),u1_struct_0(D_683),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_683) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_4890,c_72,c_70,c_4901])).

tff(c_26,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( m1_subset_1(k2_tmap_1(A_37,B_38,C_39,D_40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_40),u1_struct_0(B_38))))
      | ~ l1_struct_0(D_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_37),u1_struct_0(B_38))))
      | ~ v1_funct_2(C_39,u1_struct_0(A_37),u1_struct_0(B_38))
      | ~ v1_funct_1(C_39)
      | ~ l1_struct_0(B_38)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5269,plain,(
    ! [D_774,D_772,C_773,B_771,A_770] :
      ( k2_partfun1(u1_struct_0(D_772),u1_struct_0(B_771),k2_tmap_1(A_770,B_771,C_773,D_772),u1_struct_0(D_774)) = k2_tmap_1(D_772,B_771,k2_tmap_1(A_770,B_771,C_773,D_772),D_774)
      | ~ m1_pre_topc(D_774,D_772)
      | ~ v1_funct_2(k2_tmap_1(A_770,B_771,C_773,D_772),u1_struct_0(D_772),u1_struct_0(B_771))
      | ~ v1_funct_1(k2_tmap_1(A_770,B_771,C_773,D_772))
      | ~ l1_pre_topc(B_771)
      | ~ v2_pre_topc(B_771)
      | v2_struct_0(B_771)
      | ~ l1_pre_topc(D_772)
      | ~ v2_pre_topc(D_772)
      | v2_struct_0(D_772)
      | ~ l1_struct_0(D_772)
      | ~ m1_subset_1(C_773,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_770),u1_struct_0(B_771))))
      | ~ v1_funct_2(C_773,u1_struct_0(A_770),u1_struct_0(B_771))
      | ~ v1_funct_1(C_773)
      | ~ l1_struct_0(B_771)
      | ~ l1_struct_0(A_770) ) ),
    inference(resolution,[status(thm)],[c_26,c_4973])).

tff(c_5273,plain,(
    ! [D_772,D_774] :
      ( k2_partfun1(u1_struct_0(D_772),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_772),u1_struct_0(D_774)) = k2_tmap_1(D_772,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_772),D_774)
      | ~ m1_pre_topc(D_774,D_772)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_772),u1_struct_0(D_772),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_772))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(D_772)
      | ~ v2_pre_topc(D_772)
      | v2_struct_0(D_772)
      | ~ l1_struct_0(D_772)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_5269])).

tff(c_5277,plain,(
    ! [D_772,D_774] :
      ( k2_partfun1(u1_struct_0(D_772),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_772),u1_struct_0(D_774)) = k2_tmap_1(D_772,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_772),D_774)
      | ~ m1_pre_topc(D_774,D_772)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_772),u1_struct_0(D_772),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_772))
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(D_772)
      | ~ v2_pre_topc(D_772)
      | v2_struct_0(D_772)
      | ~ l1_struct_0(D_772) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_4890,c_72,c_70,c_76,c_74,c_5273])).

tff(c_5279,plain,(
    ! [D_775,D_776] :
      ( k2_partfun1(u1_struct_0(D_775),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_775),u1_struct_0(D_776)) = k2_tmap_1(D_775,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_775),D_776)
      | ~ m1_pre_topc(D_776,D_775)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_775),u1_struct_0(D_775),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_775))
      | ~ l1_pre_topc(D_775)
      | ~ v2_pre_topc(D_775)
      | v2_struct_0(D_775)
      | ~ l1_struct_0(D_775) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5277])).

tff(c_4906,plain,(
    ! [A_685,B_686,C_687,D_688] :
      ( m1_subset_1(k2_tmap_1(A_685,B_686,C_687,D_688),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_688),u1_struct_0(B_686))))
      | ~ l1_struct_0(D_688)
      | ~ m1_subset_1(C_687,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_685),u1_struct_0(B_686))))
      | ~ v1_funct_2(C_687,u1_struct_0(A_685),u1_struct_0(B_686))
      | ~ v1_funct_1(C_687)
      | ~ l1_struct_0(B_686)
      | ~ l1_struct_0(A_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k2_partfun1(A_11,B_12,C_13,D_14) = k7_relat_1(C_13,D_14)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5044,plain,(
    ! [D_712,A_711,D_713,C_710,B_714] :
      ( k2_partfun1(u1_struct_0(D_713),u1_struct_0(B_714),k2_tmap_1(A_711,B_714,C_710,D_713),D_712) = k7_relat_1(k2_tmap_1(A_711,B_714,C_710,D_713),D_712)
      | ~ v1_funct_1(k2_tmap_1(A_711,B_714,C_710,D_713))
      | ~ l1_struct_0(D_713)
      | ~ m1_subset_1(C_710,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_711),u1_struct_0(B_714))))
      | ~ v1_funct_2(C_710,u1_struct_0(A_711),u1_struct_0(B_714))
      | ~ v1_funct_1(C_710)
      | ~ l1_struct_0(B_714)
      | ~ l1_struct_0(A_711) ) ),
    inference(resolution,[status(thm)],[c_4906,c_12])).

tff(c_5048,plain,(
    ! [D_713,D_712] :
      ( k2_partfun1(u1_struct_0(D_713),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_713),D_712) = k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_713),D_712)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_713))
      | ~ l1_struct_0(D_713)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_5044])).

tff(c_5052,plain,(
    ! [D_713,D_712] :
      ( k2_partfun1(u1_struct_0(D_713),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_713),D_712) = k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_713),D_712)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_713))
      | ~ l1_struct_0(D_713) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_4890,c_72,c_70,c_5048])).

tff(c_5301,plain,(
    ! [D_777,D_778] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_777),u1_struct_0(D_778)) = k2_tmap_1(D_777,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_777),D_778)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_777))
      | ~ l1_struct_0(D_777)
      | ~ m1_pre_topc(D_778,D_777)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_777),u1_struct_0(D_777),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_777))
      | ~ l1_pre_topc(D_777)
      | ~ v2_pre_topc(D_777)
      | v2_struct_0(D_777)
      | ~ l1_struct_0(D_777) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5279,c_5052])).

tff(c_5310,plain,(
    ! [D_779,D_780] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_779),u1_struct_0(D_780)) = k2_tmap_1(D_779,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_779),D_780)
      | ~ m1_pre_topc(D_780,D_779)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_779))
      | ~ l1_pre_topc(D_779)
      | ~ v2_pre_topc(D_779)
      | v2_struct_0(D_779)
      | ~ l1_struct_0(D_779) ) ),
    inference(resolution,[status(thm)],[c_4904,c_5301])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4921,plain,(
    ! [A_685,B_686,C_687,D_688] :
      ( v1_relat_1(k2_tmap_1(A_685,B_686,C_687,D_688))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(D_688),u1_struct_0(B_686)))
      | ~ l1_struct_0(D_688)
      | ~ m1_subset_1(C_687,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_685),u1_struct_0(B_686))))
      | ~ v1_funct_2(C_687,u1_struct_0(A_685),u1_struct_0(B_686))
      | ~ v1_funct_1(C_687)
      | ~ l1_struct_0(B_686)
      | ~ l1_struct_0(A_685) ) ),
    inference(resolution,[status(thm)],[c_4906,c_2])).

tff(c_4930,plain,(
    ! [A_689,B_690,C_691,D_692] :
      ( v1_relat_1(k2_tmap_1(A_689,B_690,C_691,D_692))
      | ~ l1_struct_0(D_692)
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_689),u1_struct_0(B_690))))
      | ~ v1_funct_2(C_691,u1_struct_0(A_689),u1_struct_0(B_690))
      | ~ v1_funct_1(C_691)
      | ~ l1_struct_0(B_690)
      | ~ l1_struct_0(A_689) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4921])).

tff(c_5083,plain,(
    ! [B_725,C_728,D_727,A_724,D_726] :
      ( v1_relat_1(k2_tmap_1(D_726,B_725,k2_tmap_1(A_724,B_725,C_728,D_726),D_727))
      | ~ l1_struct_0(D_727)
      | ~ v1_funct_2(k2_tmap_1(A_724,B_725,C_728,D_726),u1_struct_0(D_726),u1_struct_0(B_725))
      | ~ v1_funct_1(k2_tmap_1(A_724,B_725,C_728,D_726))
      | ~ l1_struct_0(D_726)
      | ~ m1_subset_1(C_728,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_724),u1_struct_0(B_725))))
      | ~ v1_funct_2(C_728,u1_struct_0(A_724),u1_struct_0(B_725))
      | ~ v1_funct_1(C_728)
      | ~ l1_struct_0(B_725)
      | ~ l1_struct_0(A_724) ) ),
    inference(resolution,[status(thm)],[c_26,c_4930])).

tff(c_5087,plain,(
    ! [D_683,D_727] :
      ( v1_relat_1(k2_tmap_1(D_683,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683),D_727))
      | ~ l1_struct_0(D_727)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(D_683) ) ),
    inference(resolution,[status(thm)],[c_4904,c_5083])).

tff(c_5092,plain,(
    ! [D_683,D_727] :
      ( v1_relat_1(k2_tmap_1(D_683,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683),D_727))
      | ~ l1_struct_0(D_727)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683))
      | ~ l1_struct_0(D_683) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_4890,c_72,c_70,c_68,c_5087])).

tff(c_5400,plain,(
    ! [D_781,D_782] :
      ( v1_relat_1(k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_781),u1_struct_0(D_782)))
      | ~ l1_struct_0(D_782)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_781))
      | ~ l1_struct_0(D_781)
      | ~ m1_pre_topc(D_782,D_781)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_781))
      | ~ l1_pre_topc(D_781)
      | ~ v2_pre_topc(D_781)
      | v2_struct_0(D_781)
      | ~ l1_struct_0(D_781) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5310,c_5092])).

tff(c_5406,plain,(
    ! [D_782] :
      ( v1_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_782)))
      | ~ l1_struct_0(D_782)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
      | ~ l1_struct_0('#skF_1')
      | ~ m1_pre_topc(D_782,'#skF_1')
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4998,c_5400])).

tff(c_5411,plain,(
    ! [D_782] :
      ( v1_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_782)))
      | ~ l1_struct_0(D_782)
      | ~ m1_pre_topc(D_782,'#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_82,c_80,c_72,c_4998,c_4880,c_72,c_4998,c_5406])).

tff(c_5412,plain,(
    ! [D_782] :
      ( v1_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_782)))
      | ~ l1_struct_0(D_782)
      | ~ m1_pre_topc(D_782,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5411])).

tff(c_4982,plain,(
    ! [D_708] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_708)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_708)
      | ~ m1_pre_topc(D_708,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_4981])).

tff(c_10,plain,(
    ! [C_10,A_8,B_9] :
      ( v4_relat_1(C_10,A_8)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4940,plain,(
    ! [A_694,B_695,C_696,D_697] :
      ( v4_relat_1(k2_tmap_1(A_694,B_695,C_696,D_697),u1_struct_0(D_697))
      | ~ l1_struct_0(D_697)
      | ~ m1_subset_1(C_696,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_694),u1_struct_0(B_695))))
      | ~ v1_funct_2(C_696,u1_struct_0(A_694),u1_struct_0(B_695))
      | ~ v1_funct_1(C_696)
      | ~ l1_struct_0(B_695)
      | ~ l1_struct_0(A_694) ) ),
    inference(resolution,[status(thm)],[c_4906,c_10])).

tff(c_5117,plain,(
    ! [D_738,D_739,B_737,A_736,C_740] :
      ( v4_relat_1(k2_tmap_1(D_738,B_737,k2_tmap_1(A_736,B_737,C_740,D_738),D_739),u1_struct_0(D_739))
      | ~ l1_struct_0(D_739)
      | ~ v1_funct_2(k2_tmap_1(A_736,B_737,C_740,D_738),u1_struct_0(D_738),u1_struct_0(B_737))
      | ~ v1_funct_1(k2_tmap_1(A_736,B_737,C_740,D_738))
      | ~ l1_struct_0(D_738)
      | ~ m1_subset_1(C_740,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_736),u1_struct_0(B_737))))
      | ~ v1_funct_2(C_740,u1_struct_0(A_736),u1_struct_0(B_737))
      | ~ v1_funct_1(C_740)
      | ~ l1_struct_0(B_737)
      | ~ l1_struct_0(A_736) ) ),
    inference(resolution,[status(thm)],[c_26,c_4940])).

tff(c_5121,plain,(
    ! [D_683,D_739] :
      ( v4_relat_1(k2_tmap_1(D_683,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683),D_739),u1_struct_0(D_739))
      | ~ l1_struct_0(D_739)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(D_683) ) ),
    inference(resolution,[status(thm)],[c_4904,c_5117])).

tff(c_5126,plain,(
    ! [D_683,D_739] :
      ( v4_relat_1(k2_tmap_1(D_683,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683),D_739),u1_struct_0(D_739))
      | ~ l1_struct_0(D_739)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683))
      | ~ l1_struct_0(D_683) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_4890,c_72,c_70,c_68,c_5121])).

tff(c_5483,plain,(
    ! [D_794,D_795] :
      ( v4_relat_1(k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_794),u1_struct_0(D_795)),u1_struct_0(D_795))
      | ~ l1_struct_0(D_795)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_794))
      | ~ l1_struct_0(D_794)
      | ~ m1_pre_topc(D_795,D_794)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_794))
      | ~ l1_pre_topc(D_794)
      | ~ v2_pre_topc(D_794)
      | v2_struct_0(D_794)
      | ~ l1_struct_0(D_794) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5310,c_5126])).

tff(c_5492,plain,(
    ! [D_795] :
      ( v4_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_795)),u1_struct_0(D_795))
      | ~ l1_struct_0(D_795)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
      | ~ l1_struct_0('#skF_1')
      | ~ m1_pre_topc(D_795,'#skF_1')
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4998,c_5483])).

tff(c_5498,plain,(
    ! [D_795] :
      ( v4_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_795)),u1_struct_0(D_795))
      | ~ l1_struct_0(D_795)
      | ~ m1_pre_topc(D_795,'#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_82,c_80,c_72,c_4998,c_4880,c_72,c_4998,c_5492])).

tff(c_5500,plain,(
    ! [D_796] :
      ( v4_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_796)),u1_struct_0(D_796))
      | ~ l1_struct_0(D_796)
      | ~ m1_pre_topc(D_796,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5498])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5513,plain,(
    ! [D_797] :
      ( k7_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_797)),u1_struct_0(D_797)) = k7_relat_1('#skF_3',u1_struct_0(D_797))
      | ~ v1_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_797)))
      | ~ l1_struct_0(D_797)
      | ~ m1_pre_topc(D_797,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_5500,c_6])).

tff(c_5530,plain,(
    ! [D_798] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_798),u1_struct_0(D_798)) = k7_relat_1('#skF_3',u1_struct_0(D_798))
      | ~ v1_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_798)))
      | ~ l1_struct_0(D_798)
      | ~ m1_pre_topc(D_798,'#skF_1')
      | ~ m1_pre_topc(D_798,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4982,c_5513])).

tff(c_5565,plain,(
    ! [D_804] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_804),u1_struct_0(D_804)) = k7_relat_1('#skF_3',u1_struct_0(D_804))
      | ~ l1_struct_0(D_804)
      | ~ m1_pre_topc(D_804,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_5412,c_5530])).

tff(c_5309,plain,(
    ! [D_683,D_778] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683),u1_struct_0(D_778)) = k2_tmap_1(D_683,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683),D_778)
      | ~ m1_pre_topc(D_778,D_683)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_683))
      | ~ l1_pre_topc(D_683)
      | ~ v2_pre_topc(D_683)
      | v2_struct_0(D_683)
      | ~ l1_struct_0(D_683) ) ),
    inference(resolution,[status(thm)],[c_4904,c_5301])).

tff(c_5601,plain,(
    ! [D_805] :
      ( k2_tmap_1(D_805,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_805),D_805) = k7_relat_1('#skF_3',u1_struct_0(D_805))
      | ~ m1_pre_topc(D_805,D_805)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_805))
      | ~ l1_pre_topc(D_805)
      | ~ v2_pre_topc(D_805)
      | v2_struct_0(D_805)
      | ~ l1_struct_0(D_805)
      | ~ l1_struct_0(D_805)
      | ~ m1_pre_topc(D_805,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5565,c_5309])).

tff(c_5613,plain,(
    ! [D_675] :
      ( k2_tmap_1(D_675,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_675),D_675) = k7_relat_1('#skF_3',u1_struct_0(D_675))
      | ~ m1_pre_topc(D_675,D_675)
      | ~ l1_pre_topc(D_675)
      | ~ v2_pre_topc(D_675)
      | v2_struct_0(D_675)
      | ~ m1_pre_topc(D_675,'#skF_1')
      | ~ l1_struct_0(D_675) ) ),
    inference(resolution,[status(thm)],[c_4889,c_5601])).

tff(c_5540,plain,(
    ! [D_803,E_800,B_801,A_799,C_802] :
      ( v5_pre_topc(k2_tmap_1(A_799,B_801,E_800,D_803),D_803,B_801)
      | ~ m1_subset_1(k2_tmap_1(A_799,B_801,E_800,k1_tsep_1(A_799,C_802,D_803)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_799,C_802,D_803)),u1_struct_0(B_801))))
      | ~ v5_pre_topc(k2_tmap_1(A_799,B_801,E_800,k1_tsep_1(A_799,C_802,D_803)),k1_tsep_1(A_799,C_802,D_803),B_801)
      | ~ v1_funct_2(k2_tmap_1(A_799,B_801,E_800,k1_tsep_1(A_799,C_802,D_803)),u1_struct_0(k1_tsep_1(A_799,C_802,D_803)),u1_struct_0(B_801))
      | ~ v1_funct_1(k2_tmap_1(A_799,B_801,E_800,k1_tsep_1(A_799,C_802,D_803)))
      | ~ m1_subset_1(E_800,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_799),u1_struct_0(B_801))))
      | ~ v1_funct_2(E_800,u1_struct_0(A_799),u1_struct_0(B_801))
      | ~ v1_funct_1(E_800)
      | ~ r4_tsep_1(A_799,C_802,D_803)
      | ~ m1_pre_topc(D_803,A_799)
      | v2_struct_0(D_803)
      | ~ m1_pre_topc(C_802,A_799)
      | v2_struct_0(C_802)
      | ~ l1_pre_topc(B_801)
      | ~ v2_pre_topc(B_801)
      | v2_struct_0(B_801)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_5554,plain,(
    ! [B_801,E_800] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_801,E_800,'#skF_5'),'#skF_5',B_801)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_801,E_800,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_801))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_801,E_800,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_801)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_801,E_800,k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_801))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_801,E_800,k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_800,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_801))))
      | ~ v1_funct_2(E_800,u1_struct_0('#skF_1'),u1_struct_0(B_801))
      | ~ v1_funct_1(E_800)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_801)
      | ~ v2_pre_topc(B_801)
      | v2_struct_0(B_801)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_5540])).

tff(c_5563,plain,(
    ! [B_801,E_800] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_801,E_800,'#skF_5'),'#skF_5',B_801)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_801,E_800,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_801))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_801,E_800,'#skF_1'),'#skF_1',B_801)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_801,E_800,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_801))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_801,E_800,'#skF_1'))
      | ~ m1_subset_1(E_800,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_801))))
      | ~ v1_funct_2(E_800,u1_struct_0('#skF_1'),u1_struct_0(B_801))
      | ~ v1_funct_1(E_800)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_801)
      | ~ v2_pre_topc(B_801)
      | v2_struct_0(B_801)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_64,c_60,c_56,c_58,c_58,c_58,c_58,c_58,c_58,c_5554])).

tff(c_5857,plain,(
    ! [B_823,E_824] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_823,E_824,'#skF_5'),'#skF_5',B_823)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_823,E_824,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_823))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_823,E_824,'#skF_1'),'#skF_1',B_823)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_823,E_824,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_823))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_823,E_824,'#skF_1'))
      | ~ m1_subset_1(E_824,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_823))))
      | ~ v1_funct_2(E_824,u1_struct_0('#skF_1'),u1_struct_0(B_823))
      | ~ v1_funct_1(E_824)
      | ~ l1_pre_topc(B_823)
      | ~ v2_pre_topc(B_823)
      | v2_struct_0(B_823) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_66,c_62,c_5563])).

tff(c_5861,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),'#skF_5'),'#skF_5','#skF_2')
    | ~ m1_subset_1(k7_relat_1('#skF_3',u1_struct_0('#skF_1')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),'#skF_1'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),'#skF_1'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5613,c_5857])).

tff(c_5870,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_4858,c_82,c_80,c_4858,c_76,c_74,c_72,c_4998,c_70,c_4998,c_68,c_4998,c_72,c_4998,c_4998,c_70,c_4998,c_4998,c_4812,c_4998,c_4998,c_68,c_242,c_4998,c_5861])).

tff(c_5872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_4813,c_5870])).

tff(c_5874,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_5957,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5953,c_5874])).

tff(c_5960,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_5957])).

tff(c_5964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_5960])).

tff(c_5966,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_6065,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6061,c_5966])).

tff(c_6068,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_6065])).

tff(c_6072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_6068])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.79/3.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.88/3.09  
% 8.88/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.88/3.09  %$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.88/3.09  
% 8.88/3.09  %Foreground sorts:
% 8.88/3.09  
% 8.88/3.09  
% 8.88/3.09  %Background operators:
% 8.88/3.09  
% 8.88/3.09  
% 8.88/3.09  %Foreground operators:
% 8.88/3.09  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.88/3.09  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 8.88/3.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.88/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.88/3.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.88/3.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.88/3.09  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 8.88/3.09  tff('#skF_5', type, '#skF_5': $i).
% 8.88/3.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.88/3.09  tff('#skF_2', type, '#skF_2': $i).
% 8.88/3.09  tff('#skF_3', type, '#skF_3': $i).
% 8.88/3.09  tff('#skF_1', type, '#skF_1': $i).
% 8.88/3.09  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.88/3.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.88/3.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.88/3.09  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.88/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.88/3.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.88/3.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.88/3.09  tff('#skF_4', type, '#skF_4': $i).
% 8.88/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.88/3.09  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 8.88/3.09  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.88/3.09  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.88/3.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.88/3.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.88/3.09  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 8.88/3.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.88/3.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.88/3.09  
% 9.30/3.13  tff(f_253, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (((A = k1_tsep_1(A, D, E)) & r4_tsep_1(A, D, E)) => ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, C, E))) & v1_funct_2(k2_tmap_1(A, B, C, E), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, E), E, B)) & m1_subset_1(k2_tmap_1(A, B, C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_tmap_1)).
% 9.30/3.13  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.30/3.13  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.30/3.13  tff(f_130, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 9.30/3.13  tff(f_112, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 9.30/3.13  tff(f_52, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.30/3.13  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 9.30/3.13  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.30/3.13  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.30/3.13  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.30/3.13  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 9.30/3.13  tff(f_190, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_funct_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D))) & v1_funct_2(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_tsep_1(A, C, D), B)) & m1_subset_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, E, C)) & v1_funct_2(k2_tmap_1(A, B, E, C), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, C), C, B)) & m1_subset_1(k2_tmap_1(A, B, E, C), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, E, D))) & v1_funct_2(k2_tmap_1(A, B, E, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, E, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_tmap_1)).
% 9.30/3.13  tff(c_80, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_211, plain, (![B_101, A_102]: (l1_pre_topc(B_101) | ~m1_pre_topc(B_101, A_102) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.30/3.13  tff(c_214, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_211])).
% 9.30/3.13  tff(c_220, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_214])).
% 9.30/3.13  tff(c_14, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.30/3.13  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_70, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_6029, plain, (![A_861, B_862, C_863, D_864]: (v1_funct_1(k2_tmap_1(A_861, B_862, C_863, D_864)) | ~l1_struct_0(D_864) | ~m1_subset_1(C_863, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_861), u1_struct_0(B_862)))) | ~v1_funct_2(C_863, u1_struct_0(A_861), u1_struct_0(B_862)) | ~v1_funct_1(C_863) | ~l1_struct_0(B_862) | ~l1_struct_0(A_861))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.13  tff(c_6031, plain, (![D_864]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_864)) | ~l1_struct_0(D_864) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_6029])).
% 9.30/3.13  tff(c_6034, plain, (![D_864]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_864)) | ~l1_struct_0(D_864) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_6031])).
% 9.30/3.13  tff(c_6035, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_6034])).
% 9.30/3.13  tff(c_6044, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_6035])).
% 9.30/3.13  tff(c_6048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_6044])).
% 9.30/3.13  tff(c_6049, plain, (![D_864]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_864)) | ~l1_struct_0(D_864))), inference(splitRight, [status(thm)], [c_6034])).
% 9.30/3.13  tff(c_6051, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_6049])).
% 9.30/3.13  tff(c_6054, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_6051])).
% 9.30/3.13  tff(c_6058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_6054])).
% 9.30/3.13  tff(c_6061, plain, (![D_869]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_869)) | ~l1_struct_0(D_869))), inference(splitRight, [status(thm)], [c_6049])).
% 9.30/3.13  tff(c_60, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_217, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_211])).
% 9.30/3.13  tff(c_223, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_217])).
% 9.30/3.13  tff(c_5921, plain, (![A_839, B_840, C_841, D_842]: (v1_funct_1(k2_tmap_1(A_839, B_840, C_841, D_842)) | ~l1_struct_0(D_842) | ~m1_subset_1(C_841, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_839), u1_struct_0(B_840)))) | ~v1_funct_2(C_841, u1_struct_0(A_839), u1_struct_0(B_840)) | ~v1_funct_1(C_841) | ~l1_struct_0(B_840) | ~l1_struct_0(A_839))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.13  tff(c_5923, plain, (![D_842]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_842)) | ~l1_struct_0(D_842) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_5921])).
% 9.30/3.13  tff(c_5926, plain, (![D_842]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_842)) | ~l1_struct_0(D_842) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_5923])).
% 9.30/3.13  tff(c_5933, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_5926])).
% 9.30/3.13  tff(c_5936, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_5933])).
% 9.30/3.13  tff(c_5940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_5936])).
% 9.30/3.13  tff(c_5941, plain, (![D_842]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_842)) | ~l1_struct_0(D_842))), inference(splitRight, [status(thm)], [c_5926])).
% 9.30/3.13  tff(c_5943, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_5941])).
% 9.30/3.13  tff(c_5946, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_5943])).
% 9.30/3.13  tff(c_5950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_5946])).
% 9.30/3.13  tff(c_5953, plain, (![D_843]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_843)) | ~l1_struct_0(D_843))), inference(splitRight, [status(thm)], [c_5941])).
% 9.30/3.13  tff(c_84, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_4193, plain, (![A_509, B_510, C_511, D_512]: (v1_funct_1(k2_tmap_1(A_509, B_510, C_511, D_512)) | ~l1_struct_0(D_512) | ~m1_subset_1(C_511, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_509), u1_struct_0(B_510)))) | ~v1_funct_2(C_511, u1_struct_0(A_509), u1_struct_0(B_510)) | ~v1_funct_1(C_511) | ~l1_struct_0(B_510) | ~l1_struct_0(A_509))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.13  tff(c_4195, plain, (![D_512]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_512)) | ~l1_struct_0(D_512) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_4193])).
% 9.30/3.13  tff(c_4198, plain, (![D_512]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_512)) | ~l1_struct_0(D_512) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_4195])).
% 9.30/3.13  tff(c_4199, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_4198])).
% 9.30/3.13  tff(c_4202, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_4199])).
% 9.30/3.13  tff(c_4206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_4202])).
% 9.30/3.13  tff(c_4208, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_4198])).
% 9.30/3.13  tff(c_4207, plain, (![D_512]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_512)) | ~l1_struct_0(D_512))), inference(splitRight, [status(thm)], [c_4198])).
% 9.30/3.13  tff(c_4209, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_4207])).
% 9.30/3.13  tff(c_4212, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_4209])).
% 9.30/3.13  tff(c_4216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_4212])).
% 9.30/3.13  tff(c_4218, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_4207])).
% 9.30/3.13  tff(c_4227, plain, (![A_517, B_518, C_519, D_520]: (v1_funct_2(k2_tmap_1(A_517, B_518, C_519, D_520), u1_struct_0(D_520), u1_struct_0(B_518)) | ~l1_struct_0(D_520) | ~m1_subset_1(C_519, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_517), u1_struct_0(B_518)))) | ~v1_funct_2(C_519, u1_struct_0(A_517), u1_struct_0(B_518)) | ~v1_funct_1(C_519) | ~l1_struct_0(B_518) | ~l1_struct_0(A_517))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.13  tff(c_4229, plain, (![D_520]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_520), u1_struct_0(D_520), u1_struct_0('#skF_2')) | ~l1_struct_0(D_520) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_4227])).
% 9.30/3.13  tff(c_4257, plain, (![D_525]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_525), u1_struct_0(D_525), u1_struct_0('#skF_2')) | ~l1_struct_0(D_525))), inference(demodulation, [status(thm), theory('equality')], [c_4208, c_4218, c_72, c_70, c_4229])).
% 9.30/3.13  tff(c_4089, plain, (![A_481, B_482, C_483, D_484]: (v1_funct_1(k2_tmap_1(A_481, B_482, C_483, D_484)) | ~l1_struct_0(D_484) | ~m1_subset_1(C_483, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_481), u1_struct_0(B_482)))) | ~v1_funct_2(C_483, u1_struct_0(A_481), u1_struct_0(B_482)) | ~v1_funct_1(C_483) | ~l1_struct_0(B_482) | ~l1_struct_0(A_481))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.13  tff(c_4091, plain, (![D_484]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_484)) | ~l1_struct_0(D_484) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_4089])).
% 9.30/3.13  tff(c_4094, plain, (![D_484]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_484)) | ~l1_struct_0(D_484) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_4091])).
% 9.30/3.13  tff(c_4095, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_4094])).
% 9.30/3.13  tff(c_4098, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_4095])).
% 9.30/3.13  tff(c_4102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_4098])).
% 9.30/3.13  tff(c_4104, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_4094])).
% 9.30/3.13  tff(c_4103, plain, (![D_484]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_484)) | ~l1_struct_0(D_484))), inference(splitRight, [status(thm)], [c_4094])).
% 9.30/3.13  tff(c_4105, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_4103])).
% 9.30/3.13  tff(c_4114, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_4105])).
% 9.30/3.13  tff(c_4118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_4114])).
% 9.30/3.13  tff(c_4120, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_4103])).
% 9.30/3.13  tff(c_4122, plain, (![A_490, B_491, C_492, D_493]: (v1_funct_2(k2_tmap_1(A_490, B_491, C_492, D_493), u1_struct_0(D_493), u1_struct_0(B_491)) | ~l1_struct_0(D_493) | ~m1_subset_1(C_492, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_490), u1_struct_0(B_491)))) | ~v1_funct_2(C_492, u1_struct_0(A_490), u1_struct_0(B_491)) | ~v1_funct_1(C_492) | ~l1_struct_0(B_491) | ~l1_struct_0(A_490))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.13  tff(c_4124, plain, (![D_493]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_493), u1_struct_0(D_493), u1_struct_0('#skF_2')) | ~l1_struct_0(D_493) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_4122])).
% 9.30/3.13  tff(c_4128, plain, (![D_494]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_494), u1_struct_0(D_494), u1_struct_0('#skF_2')) | ~l1_struct_0(D_494))), inference(demodulation, [status(thm), theory('equality')], [c_4104, c_4120, c_72, c_70, c_4124])).
% 9.30/3.13  tff(c_3945, plain, (![A_446, B_447, C_448, D_449]: (v1_funct_1(k2_tmap_1(A_446, B_447, C_448, D_449)) | ~l1_struct_0(D_449) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_446), u1_struct_0(B_447)))) | ~v1_funct_2(C_448, u1_struct_0(A_446), u1_struct_0(B_447)) | ~v1_funct_1(C_448) | ~l1_struct_0(B_447) | ~l1_struct_0(A_446))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.13  tff(c_3947, plain, (![D_449]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_449)) | ~l1_struct_0(D_449) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_3945])).
% 9.30/3.13  tff(c_3950, plain, (![D_449]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_449)) | ~l1_struct_0(D_449) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_3947])).
% 9.30/3.13  tff(c_3957, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3950])).
% 9.30/3.13  tff(c_3960, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_3957])).
% 9.30/3.13  tff(c_3964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_3960])).
% 9.30/3.13  tff(c_3966, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3950])).
% 9.30/3.13  tff(c_3951, plain, (![A_450, B_451, C_452, D_453]: (v1_funct_2(k2_tmap_1(A_450, B_451, C_452, D_453), u1_struct_0(D_453), u1_struct_0(B_451)) | ~l1_struct_0(D_453) | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_450), u1_struct_0(B_451)))) | ~v1_funct_2(C_452, u1_struct_0(A_450), u1_struct_0(B_451)) | ~v1_funct_1(C_452) | ~l1_struct_0(B_451) | ~l1_struct_0(A_450))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.13  tff(c_3953, plain, (![D_453]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_453), u1_struct_0(D_453), u1_struct_0('#skF_2')) | ~l1_struct_0(D_453) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_3951])).
% 9.30/3.13  tff(c_3956, plain, (![D_453]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_453), u1_struct_0(D_453), u1_struct_0('#skF_2')) | ~l1_struct_0(D_453) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_3953])).
% 9.30/3.13  tff(c_3968, plain, (![D_453]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_453), u1_struct_0(D_453), u1_struct_0('#skF_2')) | ~l1_struct_0(D_453) | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3966, c_3956])).
% 9.30/3.13  tff(c_3969, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3968])).
% 9.30/3.13  tff(c_3972, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_3969])).
% 9.30/3.13  tff(c_3976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_3972])).
% 9.30/3.13  tff(c_3978, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3968])).
% 9.30/3.13  tff(c_3983, plain, (![A_456, B_457, C_458, D_459]: (m1_subset_1(k2_tmap_1(A_456, B_457, C_458, D_459), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_459), u1_struct_0(B_457)))) | ~l1_struct_0(D_459) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_456), u1_struct_0(B_457)))) | ~v1_funct_2(C_458, u1_struct_0(A_456), u1_struct_0(B_457)) | ~v1_funct_1(C_458) | ~l1_struct_0(B_457) | ~l1_struct_0(A_456))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.13  tff(c_3780, plain, (![A_409, B_410, C_411, D_412]: (v1_funct_1(k2_tmap_1(A_409, B_410, C_411, D_412)) | ~l1_struct_0(D_412) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_409), u1_struct_0(B_410)))) | ~v1_funct_2(C_411, u1_struct_0(A_409), u1_struct_0(B_410)) | ~v1_funct_1(C_411) | ~l1_struct_0(B_410) | ~l1_struct_0(A_409))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.13  tff(c_3784, plain, (![D_412]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_412)) | ~l1_struct_0(D_412) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_3780])).
% 9.30/3.13  tff(c_3790, plain, (![D_412]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_412)) | ~l1_struct_0(D_412) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_3784])).
% 9.30/3.13  tff(c_3791, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3790])).
% 9.30/3.13  tff(c_3805, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_3791])).
% 9.30/3.13  tff(c_3809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_3805])).
% 9.30/3.13  tff(c_3811, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3790])).
% 9.30/3.13  tff(c_3810, plain, (![D_412]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_412)) | ~l1_struct_0(D_412))), inference(splitRight, [status(thm)], [c_3790])).
% 9.30/3.13  tff(c_3812, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3810])).
% 9.30/3.13  tff(c_3816, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_3812])).
% 9.30/3.13  tff(c_3820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_3816])).
% 9.30/3.13  tff(c_3822, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3810])).
% 9.30/3.13  tff(c_3852, plain, (![A_425, B_426, C_427, D_428]: (m1_subset_1(k2_tmap_1(A_425, B_426, C_427, D_428), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_428), u1_struct_0(B_426)))) | ~l1_struct_0(D_428) | ~m1_subset_1(C_427, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_425), u1_struct_0(B_426)))) | ~v1_funct_2(C_427, u1_struct_0(A_425), u1_struct_0(B_426)) | ~v1_funct_1(C_427) | ~l1_struct_0(B_426) | ~l1_struct_0(A_425))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.13  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_170, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_252, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_170])).
% 9.30/3.13  tff(c_160, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_257, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_160])).
% 9.30/3.13  tff(c_150, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_255, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_150])).
% 9.30/3.13  tff(c_140, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_258, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_140])).
% 9.30/3.13  tff(c_130, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_253, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_130])).
% 9.30/3.13  tff(c_120, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_256, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_120])).
% 9.30/3.13  tff(c_110, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_254, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_110])).
% 9.30/3.13  tff(c_100, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_279, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_100])).
% 9.30/3.13  tff(c_86, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_184, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_86])).
% 9.30/3.13  tff(c_194, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_184])).
% 9.30/3.13  tff(c_204, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_194])).
% 9.30/3.13  tff(c_366, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_252, c_257, c_255, c_258, c_253, c_256, c_254, c_279, c_204])).
% 9.30/3.13  tff(c_56, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_58, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_367, plain, (![A_126, B_127, C_128]: (m1_pre_topc(k1_tsep_1(A_126, B_127, C_128), A_126) | ~m1_pre_topc(C_128, A_126) | v2_struct_0(C_128) | ~m1_pre_topc(B_127, A_126) | v2_struct_0(B_127) | ~l1_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.30/3.13  tff(c_373, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_58, c_367])).
% 9.30/3.13  tff(c_376, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_64, c_60, c_373])).
% 9.30/3.13  tff(c_377, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_84, c_66, c_62, c_376])).
% 9.30/3.13  tff(c_82, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 9.30/3.13  tff(c_308, plain, (![A_113, B_114, C_115, D_116]: (k2_partfun1(A_113, B_114, C_115, D_116)=k7_relat_1(C_115, D_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_1(C_115))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.30/3.13  tff(c_314, plain, (![D_116]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_116)=k7_relat_1('#skF_3', D_116) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_68, c_308])).
% 9.30/3.13  tff(c_323, plain, (![D_116]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_116)=k7_relat_1('#skF_3', D_116))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_314])).
% 9.30/3.13  tff(c_581, plain, (![A_172, B_173, C_174, D_175]: (k2_partfun1(u1_struct_0(A_172), u1_struct_0(B_173), C_174, u1_struct_0(D_175))=k2_tmap_1(A_172, B_173, C_174, D_175) | ~m1_pre_topc(D_175, A_172) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172), u1_struct_0(B_173)))) | ~v1_funct_2(C_174, u1_struct_0(A_172), u1_struct_0(B_173)) | ~v1_funct_1(C_174) | ~l1_pre_topc(B_173) | ~v2_pre_topc(B_173) | v2_struct_0(B_173) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.30/3.13  tff(c_589, plain, (![D_175]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_175))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_175) | ~m1_pre_topc(D_175, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_581])).
% 9.30/3.13  tff(c_601, plain, (![D_175]: (k7_relat_1('#skF_3', u1_struct_0(D_175))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_175) | ~m1_pre_topc(D_175, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_72, c_70, c_323, c_589])).
% 9.30/3.13  tff(c_608, plain, (![D_177]: (k7_relat_1('#skF_3', u1_struct_0(D_177))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_177) | ~m1_pre_topc(D_177, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_601])).
% 9.30/3.13  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.30/3.13  tff(c_224, plain, (![B_103, A_104]: (v1_relat_1(B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(A_104)) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.30/3.13  tff(c_227, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_68, c_224])).
% 9.30/3.13  tff(c_230, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_227])).
% 9.30/3.13  tff(c_231, plain, (![C_105, A_106, B_107]: (v4_relat_1(C_105, A_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.30/3.13  tff(c_235, plain, (v4_relat_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_231])).
% 9.30/3.13  tff(c_236, plain, (![B_108, A_109]: (k7_relat_1(B_108, A_109)=B_108 | ~v4_relat_1(B_108, A_109) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.30/3.13  tff(c_239, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_235, c_236])).
% 9.30/3.13  tff(c_242, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_230, c_239])).
% 9.30/3.13  tff(c_614, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_608, c_242])).
% 9.30/3.13  tff(c_623, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_377, c_614])).
% 9.30/3.13  tff(c_2880, plain, (![D_361, C_360, A_357, E_358, B_359]: (v5_pre_topc(k2_tmap_1(A_357, B_359, E_358, k1_tsep_1(A_357, C_360, D_361)), k1_tsep_1(A_357, C_360, D_361), B_359) | ~m1_subset_1(k2_tmap_1(A_357, B_359, E_358, D_361), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_361), u1_struct_0(B_359)))) | ~v5_pre_topc(k2_tmap_1(A_357, B_359, E_358, D_361), D_361, B_359) | ~v1_funct_2(k2_tmap_1(A_357, B_359, E_358, D_361), u1_struct_0(D_361), u1_struct_0(B_359)) | ~v1_funct_1(k2_tmap_1(A_357, B_359, E_358, D_361)) | ~m1_subset_1(k2_tmap_1(A_357, B_359, E_358, C_360), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360), u1_struct_0(B_359)))) | ~v5_pre_topc(k2_tmap_1(A_357, B_359, E_358, C_360), C_360, B_359) | ~v1_funct_2(k2_tmap_1(A_357, B_359, E_358, C_360), u1_struct_0(C_360), u1_struct_0(B_359)) | ~v1_funct_1(k2_tmap_1(A_357, B_359, E_358, C_360)) | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_357), u1_struct_0(B_359)))) | ~v1_funct_2(E_358, u1_struct_0(A_357), u1_struct_0(B_359)) | ~v1_funct_1(E_358) | ~r4_tsep_1(A_357, C_360, D_361) | ~m1_pre_topc(D_361, A_357) | v2_struct_0(D_361) | ~m1_pre_topc(C_360, A_357) | v2_struct_0(C_360) | ~l1_pre_topc(B_359) | ~v2_pre_topc(B_359) | v2_struct_0(B_359) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357) | v2_struct_0(A_357))), inference(cnfTransformation, [status(thm)], [f_190])).
% 9.30/3.13  tff(c_2892, plain, (![C_360]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_360, '#skF_5')), k1_tsep_1('#skF_1', C_360, '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), C_360, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), u1_struct_0(C_360), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~r4_tsep_1('#skF_1', C_360, '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_360, '#skF_1') | v2_struct_0(C_360) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_279, c_2880])).
% 9.30/3.13  tff(c_2910, plain, (![C_360]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_360, '#skF_5')), k1_tsep_1('#skF_1', C_360, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), C_360, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), u1_struct_0(C_360), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360)) | ~r4_tsep_1('#skF_1', C_360, '#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_360, '#skF_1') | v2_struct_0(C_360) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_60, c_72, c_70, c_68, c_253, c_256, c_254, c_2892])).
% 9.30/3.13  tff(c_3668, plain, (![C_390]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_390, '#skF_5')), k1_tsep_1('#skF_1', C_390, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_390), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_390), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_390), C_390, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_390), u1_struct_0(C_390), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_390)) | ~r4_tsep_1('#skF_1', C_390, '#skF_5') | ~m1_pre_topc(C_390, '#skF_1') | v2_struct_0(C_390))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_62, c_2910])).
% 9.30/3.13  tff(c_3685, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_258, c_3668])).
% 9.30/3.13  tff(c_3702, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_56, c_252, c_257, c_255, c_623, c_58, c_58, c_3685])).
% 9.30/3.13  tff(c_3704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_366, c_3702])).
% 9.30/3.13  tff(c_3706, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_100])).
% 9.30/3.13  tff(c_3861, plain, (~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3852, c_3706])).
% 9.30/3.13  tff(c_3876, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3811, c_3822, c_72, c_70, c_68, c_3861])).
% 9.30/3.13  tff(c_3884, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_14, c_3876])).
% 9.30/3.13  tff(c_3888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_3884])).
% 9.30/3.13  tff(c_3890, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_140])).
% 9.30/3.13  tff(c_3992, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3983, c_3890])).
% 9.30/3.13  tff(c_4007, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3966, c_3978, c_72, c_70, c_68, c_3992])).
% 9.30/3.13  tff(c_4025, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_4007])).
% 9.30/3.13  tff(c_4029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_4025])).
% 9.30/3.13  tff(c_4031, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_160])).
% 9.30/3.13  tff(c_4132, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4128, c_4031])).
% 9.30/3.13  tff(c_4135, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_4132])).
% 9.30/3.13  tff(c_4139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_4135])).
% 9.30/3.13  tff(c_4141, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_120])).
% 9.30/3.13  tff(c_4261, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4257, c_4141])).
% 9.30/3.13  tff(c_4264, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_14, c_4261])).
% 9.30/3.13  tff(c_4268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_4264])).
% 9.30/3.13  tff(c_4270, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_150])).
% 9.30/3.13  tff(c_4306, plain, (![A_537, B_538, C_539]: (m1_pre_topc(k1_tsep_1(A_537, B_538, C_539), A_537) | ~m1_pre_topc(C_539, A_537) | v2_struct_0(C_539) | ~m1_pre_topc(B_538, A_537) | v2_struct_0(B_538) | ~l1_pre_topc(A_537) | v2_struct_0(A_537))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.30/3.13  tff(c_4312, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_58, c_4306])).
% 9.30/3.13  tff(c_4315, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_64, c_60, c_4312])).
% 9.30/3.13  tff(c_4316, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_84, c_66, c_62, c_4315])).
% 9.30/3.13  tff(c_4274, plain, (![A_526, B_527, C_528, D_529]: (k2_partfun1(A_526, B_527, C_528, D_529)=k7_relat_1(C_528, D_529) | ~m1_subset_1(C_528, k1_zfmisc_1(k2_zfmisc_1(A_526, B_527))) | ~v1_funct_1(C_528))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.30/3.13  tff(c_4276, plain, (![D_529]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_529)=k7_relat_1('#skF_3', D_529) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_68, c_4274])).
% 9.30/3.13  tff(c_4279, plain, (![D_529]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_529)=k7_relat_1('#skF_3', D_529))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4276])).
% 9.30/3.13  tff(c_4394, plain, (![A_561, B_562, C_563, D_564]: (k2_partfun1(u1_struct_0(A_561), u1_struct_0(B_562), C_563, u1_struct_0(D_564))=k2_tmap_1(A_561, B_562, C_563, D_564) | ~m1_pre_topc(D_564, A_561) | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_561), u1_struct_0(B_562)))) | ~v1_funct_2(C_563, u1_struct_0(A_561), u1_struct_0(B_562)) | ~v1_funct_1(C_563) | ~l1_pre_topc(B_562) | ~v2_pre_topc(B_562) | v2_struct_0(B_562) | ~l1_pre_topc(A_561) | ~v2_pre_topc(A_561) | v2_struct_0(A_561))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.30/3.13  tff(c_4398, plain, (![D_564]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_564))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_564) | ~m1_pre_topc(D_564, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_4394])).
% 9.30/3.13  tff(c_4402, plain, (![D_564]: (k7_relat_1('#skF_3', u1_struct_0(D_564))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_564) | ~m1_pre_topc(D_564, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_72, c_70, c_4279, c_4398])).
% 9.30/3.13  tff(c_4404, plain, (![D_565]: (k7_relat_1('#skF_3', u1_struct_0(D_565))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_565) | ~m1_pre_topc(D_565, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_4402])).
% 9.30/3.13  tff(c_4410, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4404, c_242])).
% 9.30/3.13  tff(c_4419, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4316, c_4410])).
% 9.30/3.13  tff(c_4269, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_150])).
% 9.30/3.13  tff(c_4749, plain, (![B_649, E_648, D_651, A_647, C_650]: (v5_pre_topc(k2_tmap_1(A_647, B_649, E_648, C_650), C_650, B_649) | ~m1_subset_1(k2_tmap_1(A_647, B_649, E_648, k1_tsep_1(A_647, C_650, D_651)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_647, C_650, D_651)), u1_struct_0(B_649)))) | ~v5_pre_topc(k2_tmap_1(A_647, B_649, E_648, k1_tsep_1(A_647, C_650, D_651)), k1_tsep_1(A_647, C_650, D_651), B_649) | ~v1_funct_2(k2_tmap_1(A_647, B_649, E_648, k1_tsep_1(A_647, C_650, D_651)), u1_struct_0(k1_tsep_1(A_647, C_650, D_651)), u1_struct_0(B_649)) | ~v1_funct_1(k2_tmap_1(A_647, B_649, E_648, k1_tsep_1(A_647, C_650, D_651))) | ~m1_subset_1(E_648, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_647), u1_struct_0(B_649)))) | ~v1_funct_2(E_648, u1_struct_0(A_647), u1_struct_0(B_649)) | ~v1_funct_1(E_648) | ~r4_tsep_1(A_647, C_650, D_651) | ~m1_pre_topc(D_651, A_647) | v2_struct_0(D_651) | ~m1_pre_topc(C_650, A_647) | v2_struct_0(C_650) | ~l1_pre_topc(B_649) | ~v2_pre_topc(B_649) | v2_struct_0(B_649) | ~l1_pre_topc(A_647) | ~v2_pre_topc(A_647) | v2_struct_0(A_647))), inference(cnfTransformation, [status(thm)], [f_190])).
% 9.30/3.14  tff(c_4759, plain, (![B_649, E_648]: (v5_pre_topc(k2_tmap_1('#skF_1', B_649, E_648, '#skF_4'), '#skF_4', B_649) | ~m1_subset_1(k2_tmap_1('#skF_1', B_649, E_648, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_649)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_649, E_648, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_649) | ~v1_funct_2(k2_tmap_1('#skF_1', B_649, E_648, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_649)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_649, E_648, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_648, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_649)))) | ~v1_funct_2(E_648, u1_struct_0('#skF_1'), u1_struct_0(B_649)) | ~v1_funct_1(E_648) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_649) | ~v2_pre_topc(B_649) | v2_struct_0(B_649) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_4749])).
% 9.30/3.14  tff(c_4765, plain, (![B_649, E_648]: (v5_pre_topc(k2_tmap_1('#skF_1', B_649, E_648, '#skF_4'), '#skF_4', B_649) | ~m1_subset_1(k2_tmap_1('#skF_1', B_649, E_648, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_649)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_649, E_648, '#skF_1'), '#skF_1', B_649) | ~v1_funct_2(k2_tmap_1('#skF_1', B_649, E_648, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_649)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_649, E_648, '#skF_1')) | ~m1_subset_1(E_648, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_649)))) | ~v1_funct_2(E_648, u1_struct_0('#skF_1'), u1_struct_0(B_649)) | ~v1_funct_1(E_648) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_649) | ~v2_pre_topc(B_649) | v2_struct_0(B_649) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_64, c_60, c_56, c_58, c_58, c_58, c_58, c_58, c_58, c_4759])).
% 9.30/3.14  tff(c_4800, plain, (![B_656, E_657]: (v5_pre_topc(k2_tmap_1('#skF_1', B_656, E_657, '#skF_4'), '#skF_4', B_656) | ~m1_subset_1(k2_tmap_1('#skF_1', B_656, E_657, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_656)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_656, E_657, '#skF_1'), '#skF_1', B_656) | ~v1_funct_2(k2_tmap_1('#skF_1', B_656, E_657, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_656)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_656, E_657, '#skF_1')) | ~m1_subset_1(E_657, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_656)))) | ~v1_funct_2(E_657, u1_struct_0('#skF_1'), u1_struct_0(B_656)) | ~v1_funct_1(E_657) | ~l1_pre_topc(B_656) | ~v2_pre_topc(B_656) | v2_struct_0(B_656))), inference(negUnitSimplification, [status(thm)], [c_84, c_66, c_62, c_4765])).
% 9.30/3.14  tff(c_4803, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4419, c_4800])).
% 9.30/3.14  tff(c_4809, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_72, c_4419, c_70, c_4419, c_4269, c_4419, c_68, c_4803])).
% 9.30/3.14  tff(c_4811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4270, c_4809])).
% 9.30/3.14  tff(c_4813, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_110])).
% 9.30/3.14  tff(c_4859, plain, (![A_672, B_673, C_674, D_675]: (v1_funct_1(k2_tmap_1(A_672, B_673, C_674, D_675)) | ~l1_struct_0(D_675) | ~m1_subset_1(C_674, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_672), u1_struct_0(B_673)))) | ~v1_funct_2(C_674, u1_struct_0(A_672), u1_struct_0(B_673)) | ~v1_funct_1(C_674) | ~l1_struct_0(B_673) | ~l1_struct_0(A_672))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.14  tff(c_4861, plain, (![D_675]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_675)) | ~l1_struct_0(D_675) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_4859])).
% 9.30/3.14  tff(c_4864, plain, (![D_675]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_675)) | ~l1_struct_0(D_675) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_4861])).
% 9.30/3.14  tff(c_4871, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_4864])).
% 9.30/3.14  tff(c_4874, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_4871])).
% 9.30/3.14  tff(c_4878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_4874])).
% 9.30/3.14  tff(c_4880, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_4864])).
% 9.30/3.14  tff(c_4848, plain, (![A_669, B_670, C_671]: (m1_pre_topc(k1_tsep_1(A_669, B_670, C_671), A_669) | ~m1_pre_topc(C_671, A_669) | v2_struct_0(C_671) | ~m1_pre_topc(B_670, A_669) | v2_struct_0(B_670) | ~l1_pre_topc(A_669) | v2_struct_0(A_669))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.30/3.14  tff(c_4854, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_58, c_4848])).
% 9.30/3.14  tff(c_4857, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_64, c_60, c_4854])).
% 9.30/3.14  tff(c_4858, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_84, c_66, c_62, c_4857])).
% 9.30/3.14  tff(c_4818, plain, (![A_658, B_659, C_660, D_661]: (k2_partfun1(A_658, B_659, C_660, D_661)=k7_relat_1(C_660, D_661) | ~m1_subset_1(C_660, k1_zfmisc_1(k2_zfmisc_1(A_658, B_659))) | ~v1_funct_1(C_660))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.30/3.14  tff(c_4820, plain, (![D_661]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_661)=k7_relat_1('#skF_3', D_661) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_68, c_4818])).
% 9.30/3.14  tff(c_4823, plain, (![D_661]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_661)=k7_relat_1('#skF_3', D_661))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4820])).
% 9.30/3.14  tff(c_4973, plain, (![A_705, B_706, C_707, D_708]: (k2_partfun1(u1_struct_0(A_705), u1_struct_0(B_706), C_707, u1_struct_0(D_708))=k2_tmap_1(A_705, B_706, C_707, D_708) | ~m1_pre_topc(D_708, A_705) | ~m1_subset_1(C_707, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_705), u1_struct_0(B_706)))) | ~v1_funct_2(C_707, u1_struct_0(A_705), u1_struct_0(B_706)) | ~v1_funct_1(C_707) | ~l1_pre_topc(B_706) | ~v2_pre_topc(B_706) | v2_struct_0(B_706) | ~l1_pre_topc(A_705) | ~v2_pre_topc(A_705) | v2_struct_0(A_705))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.30/3.14  tff(c_4977, plain, (![D_708]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_708))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_708) | ~m1_pre_topc(D_708, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_4973])).
% 9.30/3.14  tff(c_4981, plain, (![D_708]: (k7_relat_1('#skF_3', u1_struct_0(D_708))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_708) | ~m1_pre_topc(D_708, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_72, c_70, c_4823, c_4977])).
% 9.30/3.14  tff(c_4983, plain, (![D_709]: (k7_relat_1('#skF_3', u1_struct_0(D_709))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_709) | ~m1_pre_topc(D_709, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_4981])).
% 9.30/3.14  tff(c_4989, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4983, c_242])).
% 9.30/3.14  tff(c_4998, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4858, c_4989])).
% 9.30/3.14  tff(c_4812, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_110])).
% 9.30/3.14  tff(c_4879, plain, (![D_675]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_675)) | ~l1_struct_0(D_675))), inference(splitRight, [status(thm)], [c_4864])).
% 9.30/3.14  tff(c_4881, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_4879])).
% 9.30/3.14  tff(c_4884, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_4881])).
% 9.30/3.14  tff(c_4888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_4884])).
% 9.30/3.14  tff(c_4889, plain, (![D_675]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_675)) | ~l1_struct_0(D_675))), inference(splitRight, [status(thm)], [c_4879])).
% 9.30/3.14  tff(c_4890, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_4879])).
% 9.30/3.14  tff(c_4899, plain, (![A_680, B_681, C_682, D_683]: (v1_funct_2(k2_tmap_1(A_680, B_681, C_682, D_683), u1_struct_0(D_683), u1_struct_0(B_681)) | ~l1_struct_0(D_683) | ~m1_subset_1(C_682, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_680), u1_struct_0(B_681)))) | ~v1_funct_2(C_682, u1_struct_0(A_680), u1_struct_0(B_681)) | ~v1_funct_1(C_682) | ~l1_struct_0(B_681) | ~l1_struct_0(A_680))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.14  tff(c_4901, plain, (![D_683]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683), u1_struct_0(D_683), u1_struct_0('#skF_2')) | ~l1_struct_0(D_683) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_4899])).
% 9.30/3.14  tff(c_4904, plain, (![D_683]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683), u1_struct_0(D_683), u1_struct_0('#skF_2')) | ~l1_struct_0(D_683))), inference(demodulation, [status(thm), theory('equality')], [c_4880, c_4890, c_72, c_70, c_4901])).
% 9.30/3.14  tff(c_26, plain, (![A_37, B_38, C_39, D_40]: (m1_subset_1(k2_tmap_1(A_37, B_38, C_39, D_40), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_40), u1_struct_0(B_38)))) | ~l1_struct_0(D_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_37), u1_struct_0(B_38)))) | ~v1_funct_2(C_39, u1_struct_0(A_37), u1_struct_0(B_38)) | ~v1_funct_1(C_39) | ~l1_struct_0(B_38) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.14  tff(c_5269, plain, (![D_774, D_772, C_773, B_771, A_770]: (k2_partfun1(u1_struct_0(D_772), u1_struct_0(B_771), k2_tmap_1(A_770, B_771, C_773, D_772), u1_struct_0(D_774))=k2_tmap_1(D_772, B_771, k2_tmap_1(A_770, B_771, C_773, D_772), D_774) | ~m1_pre_topc(D_774, D_772) | ~v1_funct_2(k2_tmap_1(A_770, B_771, C_773, D_772), u1_struct_0(D_772), u1_struct_0(B_771)) | ~v1_funct_1(k2_tmap_1(A_770, B_771, C_773, D_772)) | ~l1_pre_topc(B_771) | ~v2_pre_topc(B_771) | v2_struct_0(B_771) | ~l1_pre_topc(D_772) | ~v2_pre_topc(D_772) | v2_struct_0(D_772) | ~l1_struct_0(D_772) | ~m1_subset_1(C_773, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_770), u1_struct_0(B_771)))) | ~v1_funct_2(C_773, u1_struct_0(A_770), u1_struct_0(B_771)) | ~v1_funct_1(C_773) | ~l1_struct_0(B_771) | ~l1_struct_0(A_770))), inference(resolution, [status(thm)], [c_26, c_4973])).
% 9.30/3.14  tff(c_5273, plain, (![D_772, D_774]: (k2_partfun1(u1_struct_0(D_772), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_772), u1_struct_0(D_774))=k2_tmap_1(D_772, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_772), D_774) | ~m1_pre_topc(D_774, D_772) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_772), u1_struct_0(D_772), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_772)) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(D_772) | ~v2_pre_topc(D_772) | v2_struct_0(D_772) | ~l1_struct_0(D_772) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_5269])).
% 9.30/3.14  tff(c_5277, plain, (![D_772, D_774]: (k2_partfun1(u1_struct_0(D_772), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_772), u1_struct_0(D_774))=k2_tmap_1(D_772, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_772), D_774) | ~m1_pre_topc(D_774, D_772) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_772), u1_struct_0(D_772), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_772)) | v2_struct_0('#skF_2') | ~l1_pre_topc(D_772) | ~v2_pre_topc(D_772) | v2_struct_0(D_772) | ~l1_struct_0(D_772))), inference(demodulation, [status(thm), theory('equality')], [c_4880, c_4890, c_72, c_70, c_76, c_74, c_5273])).
% 9.30/3.14  tff(c_5279, plain, (![D_775, D_776]: (k2_partfun1(u1_struct_0(D_775), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_775), u1_struct_0(D_776))=k2_tmap_1(D_775, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_775), D_776) | ~m1_pre_topc(D_776, D_775) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_775), u1_struct_0(D_775), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_775)) | ~l1_pre_topc(D_775) | ~v2_pre_topc(D_775) | v2_struct_0(D_775) | ~l1_struct_0(D_775))), inference(negUnitSimplification, [status(thm)], [c_78, c_5277])).
% 9.30/3.14  tff(c_4906, plain, (![A_685, B_686, C_687, D_688]: (m1_subset_1(k2_tmap_1(A_685, B_686, C_687, D_688), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_688), u1_struct_0(B_686)))) | ~l1_struct_0(D_688) | ~m1_subset_1(C_687, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_685), u1_struct_0(B_686)))) | ~v1_funct_2(C_687, u1_struct_0(A_685), u1_struct_0(B_686)) | ~v1_funct_1(C_687) | ~l1_struct_0(B_686) | ~l1_struct_0(A_685))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.30/3.14  tff(c_12, plain, (![A_11, B_12, C_13, D_14]: (k2_partfun1(A_11, B_12, C_13, D_14)=k7_relat_1(C_13, D_14) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.30/3.14  tff(c_5044, plain, (![D_712, A_711, D_713, C_710, B_714]: (k2_partfun1(u1_struct_0(D_713), u1_struct_0(B_714), k2_tmap_1(A_711, B_714, C_710, D_713), D_712)=k7_relat_1(k2_tmap_1(A_711, B_714, C_710, D_713), D_712) | ~v1_funct_1(k2_tmap_1(A_711, B_714, C_710, D_713)) | ~l1_struct_0(D_713) | ~m1_subset_1(C_710, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_711), u1_struct_0(B_714)))) | ~v1_funct_2(C_710, u1_struct_0(A_711), u1_struct_0(B_714)) | ~v1_funct_1(C_710) | ~l1_struct_0(B_714) | ~l1_struct_0(A_711))), inference(resolution, [status(thm)], [c_4906, c_12])).
% 9.30/3.14  tff(c_5048, plain, (![D_713, D_712]: (k2_partfun1(u1_struct_0(D_713), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_713), D_712)=k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_713), D_712) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_713)) | ~l1_struct_0(D_713) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_5044])).
% 9.30/3.14  tff(c_5052, plain, (![D_713, D_712]: (k2_partfun1(u1_struct_0(D_713), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_713), D_712)=k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_713), D_712) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_713)) | ~l1_struct_0(D_713))), inference(demodulation, [status(thm), theory('equality')], [c_4880, c_4890, c_72, c_70, c_5048])).
% 9.30/3.14  tff(c_5301, plain, (![D_777, D_778]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_777), u1_struct_0(D_778))=k2_tmap_1(D_777, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_777), D_778) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_777)) | ~l1_struct_0(D_777) | ~m1_pre_topc(D_778, D_777) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_777), u1_struct_0(D_777), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_777)) | ~l1_pre_topc(D_777) | ~v2_pre_topc(D_777) | v2_struct_0(D_777) | ~l1_struct_0(D_777))), inference(superposition, [status(thm), theory('equality')], [c_5279, c_5052])).
% 9.30/3.14  tff(c_5310, plain, (![D_779, D_780]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_779), u1_struct_0(D_780))=k2_tmap_1(D_779, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_779), D_780) | ~m1_pre_topc(D_780, D_779) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_779)) | ~l1_pre_topc(D_779) | ~v2_pre_topc(D_779) | v2_struct_0(D_779) | ~l1_struct_0(D_779))), inference(resolution, [status(thm)], [c_4904, c_5301])).
% 9.30/3.14  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.30/3.14  tff(c_4921, plain, (![A_685, B_686, C_687, D_688]: (v1_relat_1(k2_tmap_1(A_685, B_686, C_687, D_688)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(D_688), u1_struct_0(B_686))) | ~l1_struct_0(D_688) | ~m1_subset_1(C_687, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_685), u1_struct_0(B_686)))) | ~v1_funct_2(C_687, u1_struct_0(A_685), u1_struct_0(B_686)) | ~v1_funct_1(C_687) | ~l1_struct_0(B_686) | ~l1_struct_0(A_685))), inference(resolution, [status(thm)], [c_4906, c_2])).
% 9.30/3.14  tff(c_4930, plain, (![A_689, B_690, C_691, D_692]: (v1_relat_1(k2_tmap_1(A_689, B_690, C_691, D_692)) | ~l1_struct_0(D_692) | ~m1_subset_1(C_691, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_689), u1_struct_0(B_690)))) | ~v1_funct_2(C_691, u1_struct_0(A_689), u1_struct_0(B_690)) | ~v1_funct_1(C_691) | ~l1_struct_0(B_690) | ~l1_struct_0(A_689))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4921])).
% 9.30/3.14  tff(c_5083, plain, (![B_725, C_728, D_727, A_724, D_726]: (v1_relat_1(k2_tmap_1(D_726, B_725, k2_tmap_1(A_724, B_725, C_728, D_726), D_727)) | ~l1_struct_0(D_727) | ~v1_funct_2(k2_tmap_1(A_724, B_725, C_728, D_726), u1_struct_0(D_726), u1_struct_0(B_725)) | ~v1_funct_1(k2_tmap_1(A_724, B_725, C_728, D_726)) | ~l1_struct_0(D_726) | ~m1_subset_1(C_728, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_724), u1_struct_0(B_725)))) | ~v1_funct_2(C_728, u1_struct_0(A_724), u1_struct_0(B_725)) | ~v1_funct_1(C_728) | ~l1_struct_0(B_725) | ~l1_struct_0(A_724))), inference(resolution, [status(thm)], [c_26, c_4930])).
% 9.30/3.14  tff(c_5087, plain, (![D_683, D_727]: (v1_relat_1(k2_tmap_1(D_683, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683), D_727)) | ~l1_struct_0(D_727) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | ~l1_struct_0(D_683))), inference(resolution, [status(thm)], [c_4904, c_5083])).
% 9.30/3.14  tff(c_5092, plain, (![D_683, D_727]: (v1_relat_1(k2_tmap_1(D_683, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683), D_727)) | ~l1_struct_0(D_727) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683)) | ~l1_struct_0(D_683))), inference(demodulation, [status(thm), theory('equality')], [c_4880, c_4890, c_72, c_70, c_68, c_5087])).
% 9.30/3.14  tff(c_5400, plain, (![D_781, D_782]: (v1_relat_1(k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_781), u1_struct_0(D_782))) | ~l1_struct_0(D_782) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_781)) | ~l1_struct_0(D_781) | ~m1_pre_topc(D_782, D_781) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_781)) | ~l1_pre_topc(D_781) | ~v2_pre_topc(D_781) | v2_struct_0(D_781) | ~l1_struct_0(D_781))), inference(superposition, [status(thm), theory('equality')], [c_5310, c_5092])).
% 9.30/3.14  tff(c_5406, plain, (![D_782]: (v1_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_782))) | ~l1_struct_0(D_782) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~l1_struct_0('#skF_1') | ~m1_pre_topc(D_782, '#skF_1') | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4998, c_5400])).
% 9.30/3.14  tff(c_5411, plain, (![D_782]: (v1_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_782))) | ~l1_struct_0(D_782) | ~m1_pre_topc(D_782, '#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4880, c_82, c_80, c_72, c_4998, c_4880, c_72, c_4998, c_5406])).
% 9.30/3.14  tff(c_5412, plain, (![D_782]: (v1_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_782))) | ~l1_struct_0(D_782) | ~m1_pre_topc(D_782, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_84, c_5411])).
% 9.30/3.14  tff(c_4982, plain, (![D_708]: (k7_relat_1('#skF_3', u1_struct_0(D_708))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_708) | ~m1_pre_topc(D_708, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_4981])).
% 9.30/3.14  tff(c_10, plain, (![C_10, A_8, B_9]: (v4_relat_1(C_10, A_8) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.30/3.14  tff(c_4940, plain, (![A_694, B_695, C_696, D_697]: (v4_relat_1(k2_tmap_1(A_694, B_695, C_696, D_697), u1_struct_0(D_697)) | ~l1_struct_0(D_697) | ~m1_subset_1(C_696, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_694), u1_struct_0(B_695)))) | ~v1_funct_2(C_696, u1_struct_0(A_694), u1_struct_0(B_695)) | ~v1_funct_1(C_696) | ~l1_struct_0(B_695) | ~l1_struct_0(A_694))), inference(resolution, [status(thm)], [c_4906, c_10])).
% 9.30/3.14  tff(c_5117, plain, (![D_738, D_739, B_737, A_736, C_740]: (v4_relat_1(k2_tmap_1(D_738, B_737, k2_tmap_1(A_736, B_737, C_740, D_738), D_739), u1_struct_0(D_739)) | ~l1_struct_0(D_739) | ~v1_funct_2(k2_tmap_1(A_736, B_737, C_740, D_738), u1_struct_0(D_738), u1_struct_0(B_737)) | ~v1_funct_1(k2_tmap_1(A_736, B_737, C_740, D_738)) | ~l1_struct_0(D_738) | ~m1_subset_1(C_740, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_736), u1_struct_0(B_737)))) | ~v1_funct_2(C_740, u1_struct_0(A_736), u1_struct_0(B_737)) | ~v1_funct_1(C_740) | ~l1_struct_0(B_737) | ~l1_struct_0(A_736))), inference(resolution, [status(thm)], [c_26, c_4940])).
% 9.30/3.14  tff(c_5121, plain, (![D_683, D_739]: (v4_relat_1(k2_tmap_1(D_683, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683), D_739), u1_struct_0(D_739)) | ~l1_struct_0(D_739) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | ~l1_struct_0(D_683))), inference(resolution, [status(thm)], [c_4904, c_5117])).
% 9.30/3.14  tff(c_5126, plain, (![D_683, D_739]: (v4_relat_1(k2_tmap_1(D_683, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683), D_739), u1_struct_0(D_739)) | ~l1_struct_0(D_739) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683)) | ~l1_struct_0(D_683))), inference(demodulation, [status(thm), theory('equality')], [c_4880, c_4890, c_72, c_70, c_68, c_5121])).
% 9.30/3.14  tff(c_5483, plain, (![D_794, D_795]: (v4_relat_1(k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_794), u1_struct_0(D_795)), u1_struct_0(D_795)) | ~l1_struct_0(D_795) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_794)) | ~l1_struct_0(D_794) | ~m1_pre_topc(D_795, D_794) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_794)) | ~l1_pre_topc(D_794) | ~v2_pre_topc(D_794) | v2_struct_0(D_794) | ~l1_struct_0(D_794))), inference(superposition, [status(thm), theory('equality')], [c_5310, c_5126])).
% 9.30/3.14  tff(c_5492, plain, (![D_795]: (v4_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_795)), u1_struct_0(D_795)) | ~l1_struct_0(D_795) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~l1_struct_0('#skF_1') | ~m1_pre_topc(D_795, '#skF_1') | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4998, c_5483])).
% 9.30/3.14  tff(c_5498, plain, (![D_795]: (v4_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_795)), u1_struct_0(D_795)) | ~l1_struct_0(D_795) | ~m1_pre_topc(D_795, '#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4880, c_82, c_80, c_72, c_4998, c_4880, c_72, c_4998, c_5492])).
% 9.30/3.14  tff(c_5500, plain, (![D_796]: (v4_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_796)), u1_struct_0(D_796)) | ~l1_struct_0(D_796) | ~m1_pre_topc(D_796, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_84, c_5498])).
% 9.30/3.14  tff(c_6, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.30/3.14  tff(c_5513, plain, (![D_797]: (k7_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_797)), u1_struct_0(D_797))=k7_relat_1('#skF_3', u1_struct_0(D_797)) | ~v1_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_797))) | ~l1_struct_0(D_797) | ~m1_pre_topc(D_797, '#skF_1'))), inference(resolution, [status(thm)], [c_5500, c_6])).
% 9.30/3.14  tff(c_5530, plain, (![D_798]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_798), u1_struct_0(D_798))=k7_relat_1('#skF_3', u1_struct_0(D_798)) | ~v1_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_798))) | ~l1_struct_0(D_798) | ~m1_pre_topc(D_798, '#skF_1') | ~m1_pre_topc(D_798, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4982, c_5513])).
% 9.30/3.14  tff(c_5565, plain, (![D_804]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_804), u1_struct_0(D_804))=k7_relat_1('#skF_3', u1_struct_0(D_804)) | ~l1_struct_0(D_804) | ~m1_pre_topc(D_804, '#skF_1'))), inference(resolution, [status(thm)], [c_5412, c_5530])).
% 9.30/3.14  tff(c_5309, plain, (![D_683, D_778]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683), u1_struct_0(D_778))=k2_tmap_1(D_683, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683), D_778) | ~m1_pre_topc(D_778, D_683) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_683)) | ~l1_pre_topc(D_683) | ~v2_pre_topc(D_683) | v2_struct_0(D_683) | ~l1_struct_0(D_683))), inference(resolution, [status(thm)], [c_4904, c_5301])).
% 9.30/3.14  tff(c_5601, plain, (![D_805]: (k2_tmap_1(D_805, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_805), D_805)=k7_relat_1('#skF_3', u1_struct_0(D_805)) | ~m1_pre_topc(D_805, D_805) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_805)) | ~l1_pre_topc(D_805) | ~v2_pre_topc(D_805) | v2_struct_0(D_805) | ~l1_struct_0(D_805) | ~l1_struct_0(D_805) | ~m1_pre_topc(D_805, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5565, c_5309])).
% 9.30/3.14  tff(c_5613, plain, (![D_675]: (k2_tmap_1(D_675, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_675), D_675)=k7_relat_1('#skF_3', u1_struct_0(D_675)) | ~m1_pre_topc(D_675, D_675) | ~l1_pre_topc(D_675) | ~v2_pre_topc(D_675) | v2_struct_0(D_675) | ~m1_pre_topc(D_675, '#skF_1') | ~l1_struct_0(D_675))), inference(resolution, [status(thm)], [c_4889, c_5601])).
% 9.30/3.14  tff(c_5540, plain, (![D_803, E_800, B_801, A_799, C_802]: (v5_pre_topc(k2_tmap_1(A_799, B_801, E_800, D_803), D_803, B_801) | ~m1_subset_1(k2_tmap_1(A_799, B_801, E_800, k1_tsep_1(A_799, C_802, D_803)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_799, C_802, D_803)), u1_struct_0(B_801)))) | ~v5_pre_topc(k2_tmap_1(A_799, B_801, E_800, k1_tsep_1(A_799, C_802, D_803)), k1_tsep_1(A_799, C_802, D_803), B_801) | ~v1_funct_2(k2_tmap_1(A_799, B_801, E_800, k1_tsep_1(A_799, C_802, D_803)), u1_struct_0(k1_tsep_1(A_799, C_802, D_803)), u1_struct_0(B_801)) | ~v1_funct_1(k2_tmap_1(A_799, B_801, E_800, k1_tsep_1(A_799, C_802, D_803))) | ~m1_subset_1(E_800, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_799), u1_struct_0(B_801)))) | ~v1_funct_2(E_800, u1_struct_0(A_799), u1_struct_0(B_801)) | ~v1_funct_1(E_800) | ~r4_tsep_1(A_799, C_802, D_803) | ~m1_pre_topc(D_803, A_799) | v2_struct_0(D_803) | ~m1_pre_topc(C_802, A_799) | v2_struct_0(C_802) | ~l1_pre_topc(B_801) | ~v2_pre_topc(B_801) | v2_struct_0(B_801) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799))), inference(cnfTransformation, [status(thm)], [f_190])).
% 9.30/3.14  tff(c_5554, plain, (![B_801, E_800]: (v5_pre_topc(k2_tmap_1('#skF_1', B_801, E_800, '#skF_5'), '#skF_5', B_801) | ~m1_subset_1(k2_tmap_1('#skF_1', B_801, E_800, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_801)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_801, E_800, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_801) | ~v1_funct_2(k2_tmap_1('#skF_1', B_801, E_800, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_801)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_801, E_800, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_800, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_801)))) | ~v1_funct_2(E_800, u1_struct_0('#skF_1'), u1_struct_0(B_801)) | ~v1_funct_1(E_800) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_801) | ~v2_pre_topc(B_801) | v2_struct_0(B_801) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_5540])).
% 9.30/3.14  tff(c_5563, plain, (![B_801, E_800]: (v5_pre_topc(k2_tmap_1('#skF_1', B_801, E_800, '#skF_5'), '#skF_5', B_801) | ~m1_subset_1(k2_tmap_1('#skF_1', B_801, E_800, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_801)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_801, E_800, '#skF_1'), '#skF_1', B_801) | ~v1_funct_2(k2_tmap_1('#skF_1', B_801, E_800, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_801)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_801, E_800, '#skF_1')) | ~m1_subset_1(E_800, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_801)))) | ~v1_funct_2(E_800, u1_struct_0('#skF_1'), u1_struct_0(B_801)) | ~v1_funct_1(E_800) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_801) | ~v2_pre_topc(B_801) | v2_struct_0(B_801) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_64, c_60, c_56, c_58, c_58, c_58, c_58, c_58, c_58, c_5554])).
% 9.30/3.14  tff(c_5857, plain, (![B_823, E_824]: (v5_pre_topc(k2_tmap_1('#skF_1', B_823, E_824, '#skF_5'), '#skF_5', B_823) | ~m1_subset_1(k2_tmap_1('#skF_1', B_823, E_824, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_823)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_823, E_824, '#skF_1'), '#skF_1', B_823) | ~v1_funct_2(k2_tmap_1('#skF_1', B_823, E_824, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_823)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_823, E_824, '#skF_1')) | ~m1_subset_1(E_824, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_823)))) | ~v1_funct_2(E_824, u1_struct_0('#skF_1'), u1_struct_0(B_823)) | ~v1_funct_1(E_824) | ~l1_pre_topc(B_823) | ~v2_pre_topc(B_823) | v2_struct_0(B_823))), inference(negUnitSimplification, [status(thm)], [c_84, c_66, c_62, c_5563])).
% 9.30/3.14  tff(c_5861, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_5'), '#skF_5', '#skF_2') | ~m1_subset_1(k7_relat_1('#skF_3', u1_struct_0('#skF_1')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5613, c_5857])).
% 9.30/3.14  tff(c_5870, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4880, c_4858, c_82, c_80, c_4858, c_76, c_74, c_72, c_4998, c_70, c_4998, c_68, c_4998, c_72, c_4998, c_4998, c_70, c_4998, c_4998, c_4812, c_4998, c_4998, c_68, c_242, c_4998, c_5861])).
% 9.30/3.14  tff(c_5872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_4813, c_5870])).
% 9.30/3.14  tff(c_5874, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_130])).
% 9.30/3.14  tff(c_5957, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5953, c_5874])).
% 9.30/3.14  tff(c_5960, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_14, c_5957])).
% 9.30/3.14  tff(c_5964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_5960])).
% 9.30/3.14  tff(c_5966, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_170])).
% 9.30/3.14  tff(c_6065, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_6061, c_5966])).
% 9.30/3.14  tff(c_6068, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_6065])).
% 9.30/3.14  tff(c_6072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_6068])).
% 9.30/3.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.30/3.14  
% 9.30/3.14  Inference rules
% 9.30/3.14  ----------------------
% 9.30/3.14  #Ref     : 0
% 9.30/3.14  #Sup     : 1102
% 9.30/3.14  #Fact    : 0
% 9.30/3.14  #Define  : 0
% 9.30/3.14  #Split   : 40
% 9.30/3.14  #Chain   : 0
% 9.30/3.14  #Close   : 0
% 9.30/3.14  
% 9.30/3.14  Ordering : KBO
% 9.30/3.14  
% 9.30/3.14  Simplification rules
% 9.30/3.14  ----------------------
% 9.30/3.14  #Subsume      : 351
% 9.30/3.14  #Demod        : 3879
% 9.30/3.14  #Tautology    : 329
% 9.30/3.14  #SimpNegUnit  : 350
% 9.30/3.14  #BackRed      : 0
% 9.30/3.14  
% 9.30/3.14  #Partial instantiations: 0
% 9.30/3.14  #Strategies tried      : 1
% 9.30/3.14  
% 9.30/3.14  Timing (in seconds)
% 9.30/3.14  ----------------------
% 9.30/3.14  Preprocessing        : 0.46
% 9.30/3.14  Parsing              : 0.23
% 9.30/3.14  CNF conversion       : 0.05
% 9.30/3.14  Main loop            : 1.74
% 9.30/3.14  Inferencing          : 0.59
% 9.30/3.14  Reduction            : 0.67
% 9.30/3.14  Demodulation         : 0.53
% 9.30/3.14  BG Simplification    : 0.07
% 9.30/3.14  Subsumption          : 0.34
% 9.30/3.14  Abstraction          : 0.08
% 9.30/3.14  MUC search           : 0.00
% 9.30/3.14  Cooper               : 0.00
% 9.30/3.14  Total                : 2.30
% 9.30/3.14  Index Insertion      : 0.00
% 9.30/3.14  Index Deletion       : 0.00
% 9.30/3.14  Index Matching       : 0.00
% 9.30/3.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
