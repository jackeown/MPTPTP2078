%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:06 EST 2020

% Result     : Theorem 8.78s
% Output     : CNFRefutation 9.30s
% Verified   : 
% Statistics : Number of formulae       :  310 (2143 expanded)
%              Number of leaves         :   43 ( 828 expanded)
%              Depth                    :   15
%              Number of atoms          : 1108 (20642 expanded)
%              Number of equality atoms :   51 ( 909 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_254,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_131,axiom,(
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

tff(f_113,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_91,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_191,axiom,(
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

tff(c_82,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_212,plain,(
    ! [B_99,A_100] :
      ( l1_pre_topc(B_99)
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_215,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_212])).

tff(c_221,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_215])).

tff(c_16,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_6309,plain,(
    ! [A_904,B_905,C_906,D_907] :
      ( v1_funct_1(k2_tmap_1(A_904,B_905,C_906,D_907))
      | ~ l1_struct_0(D_907)
      | ~ m1_subset_1(C_906,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_904),u1_struct_0(B_905))))
      | ~ v1_funct_2(C_906,u1_struct_0(A_904),u1_struct_0(B_905))
      | ~ v1_funct_1(C_906)
      | ~ l1_struct_0(B_905)
      | ~ l1_struct_0(A_904) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6311,plain,(
    ! [D_907] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_907))
      | ~ l1_struct_0(D_907)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_6309])).

tff(c_6314,plain,(
    ! [D_907] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_907))
      | ~ l1_struct_0(D_907)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6311])).

tff(c_6315,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6314])).

tff(c_6318,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_6315])).

tff(c_6322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6318])).

tff(c_6323,plain,(
    ! [D_907] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_907))
      | ~ l1_struct_0(D_907) ) ),
    inference(splitRight,[status(thm)],[c_6314])).

tff(c_6331,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6323])).

tff(c_6334,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_6331])).

tff(c_6338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6334])).

tff(c_6344,plain,(
    ! [D_913] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_913))
      | ~ l1_struct_0(D_913) ) ),
    inference(splitRight,[status(thm)],[c_6323])).

tff(c_62,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_218,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_212])).

tff(c_224,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_218])).

tff(c_6185,plain,(
    ! [A_874,B_875,C_876,D_877] :
      ( v1_funct_1(k2_tmap_1(A_874,B_875,C_876,D_877))
      | ~ l1_struct_0(D_877)
      | ~ m1_subset_1(C_876,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_874),u1_struct_0(B_875))))
      | ~ v1_funct_2(C_876,u1_struct_0(A_874),u1_struct_0(B_875))
      | ~ v1_funct_1(C_876)
      | ~ l1_struct_0(B_875)
      | ~ l1_struct_0(A_874) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6187,plain,(
    ! [D_877] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_877))
      | ~ l1_struct_0(D_877)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_6185])).

tff(c_6190,plain,(
    ! [D_877] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_877))
      | ~ l1_struct_0(D_877)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6187])).

tff(c_6191,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6190])).

tff(c_6194,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_6191])).

tff(c_6198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6194])).

tff(c_6199,plain,(
    ! [D_877] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_877))
      | ~ l1_struct_0(D_877) ) ),
    inference(splitRight,[status(thm)],[c_6190])).

tff(c_6201,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6199])).

tff(c_6210,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_6201])).

tff(c_6214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6210])).

tff(c_6217,plain,(
    ! [D_882] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_882))
      | ~ l1_struct_0(D_882) ) ),
    inference(splitRight,[status(thm)],[c_6199])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_3685,plain,(
    ! [A_494,B_495,C_496,D_497] :
      ( v1_funct_1(k2_tmap_1(A_494,B_495,C_496,D_497))
      | ~ l1_struct_0(D_497)
      | ~ m1_subset_1(C_496,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_494),u1_struct_0(B_495))))
      | ~ v1_funct_2(C_496,u1_struct_0(A_494),u1_struct_0(B_495))
      | ~ v1_funct_1(C_496)
      | ~ l1_struct_0(B_495)
      | ~ l1_struct_0(A_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3687,plain,(
    ! [D_497] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_497))
      | ~ l1_struct_0(D_497)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3685])).

tff(c_3690,plain,(
    ! [D_497] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_497))
      | ~ l1_struct_0(D_497)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3687])).

tff(c_3691,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3690])).

tff(c_3694,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_3691])).

tff(c_3698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3694])).

tff(c_3700,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3690])).

tff(c_3699,plain,(
    ! [D_497] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_497))
      | ~ l1_struct_0(D_497) ) ),
    inference(splitRight,[status(thm)],[c_3690])).

tff(c_3701,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3699])).

tff(c_3704,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_3701])).

tff(c_3708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3704])).

tff(c_3710,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3699])).

tff(c_3712,plain,(
    ! [A_499,B_500,C_501,D_502] :
      ( v1_funct_2(k2_tmap_1(A_499,B_500,C_501,D_502),u1_struct_0(D_502),u1_struct_0(B_500))
      | ~ l1_struct_0(D_502)
      | ~ m1_subset_1(C_501,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_499),u1_struct_0(B_500))))
      | ~ v1_funct_2(C_501,u1_struct_0(A_499),u1_struct_0(B_500))
      | ~ v1_funct_1(C_501)
      | ~ l1_struct_0(B_500)
      | ~ l1_struct_0(A_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3714,plain,(
    ! [D_502] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_502),u1_struct_0(D_502),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_502)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3712])).

tff(c_3718,plain,(
    ! [D_503] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_503),u1_struct_0(D_503),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_503) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3700,c_3710,c_74,c_72,c_3714])).

tff(c_3579,plain,(
    ! [A_468,B_469,C_470,D_471] :
      ( v1_funct_1(k2_tmap_1(A_468,B_469,C_470,D_471))
      | ~ l1_struct_0(D_471)
      | ~ m1_subset_1(C_470,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_468),u1_struct_0(B_469))))
      | ~ v1_funct_2(C_470,u1_struct_0(A_468),u1_struct_0(B_469))
      | ~ v1_funct_1(C_470)
      | ~ l1_struct_0(B_469)
      | ~ l1_struct_0(A_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3581,plain,(
    ! [D_471] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_471))
      | ~ l1_struct_0(D_471)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3579])).

tff(c_3584,plain,(
    ! [D_471] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_471))
      | ~ l1_struct_0(D_471)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3581])).

tff(c_3585,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3584])).

tff(c_3588,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_3585])).

tff(c_3592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3588])).

tff(c_3593,plain,(
    ! [D_471] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_471))
      | ~ l1_struct_0(D_471) ) ),
    inference(splitRight,[status(thm)],[c_3584])).

tff(c_3601,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3593])).

tff(c_3604,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_3601])).

tff(c_3608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3604])).

tff(c_3610,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3593])).

tff(c_3594,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3584])).

tff(c_3595,plain,(
    ! [A_472,B_473,C_474,D_475] :
      ( v1_funct_2(k2_tmap_1(A_472,B_473,C_474,D_475),u1_struct_0(D_475),u1_struct_0(B_473))
      | ~ l1_struct_0(D_475)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_472),u1_struct_0(B_473))))
      | ~ v1_funct_2(C_474,u1_struct_0(A_472),u1_struct_0(B_473))
      | ~ v1_funct_1(C_474)
      | ~ l1_struct_0(B_473)
      | ~ l1_struct_0(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3597,plain,(
    ! [D_475] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_475),u1_struct_0(D_475),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_475)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3595])).

tff(c_3600,plain,(
    ! [D_475] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_475),u1_struct_0(D_475),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_475)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3594,c_74,c_72,c_3597])).

tff(c_3613,plain,(
    ! [D_476] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_476),u1_struct_0(D_476),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3610,c_3600])).

tff(c_3437,plain,(
    ! [A_433,B_434,C_435,D_436] :
      ( v1_funct_1(k2_tmap_1(A_433,B_434,C_435,D_436))
      | ~ l1_struct_0(D_436)
      | ~ m1_subset_1(C_435,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_433),u1_struct_0(B_434))))
      | ~ v1_funct_2(C_435,u1_struct_0(A_433),u1_struct_0(B_434))
      | ~ v1_funct_1(C_435)
      | ~ l1_struct_0(B_434)
      | ~ l1_struct_0(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3439,plain,(
    ! [D_436] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_436))
      | ~ l1_struct_0(D_436)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3437])).

tff(c_3442,plain,(
    ! [D_436] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_436))
      | ~ l1_struct_0(D_436)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3439])).

tff(c_3449,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3442])).

tff(c_3452,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_3449])).

tff(c_3456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3452])).

tff(c_3458,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3442])).

tff(c_3443,plain,(
    ! [A_437,B_438,C_439,D_440] :
      ( v1_funct_2(k2_tmap_1(A_437,B_438,C_439,D_440),u1_struct_0(D_440),u1_struct_0(B_438))
      | ~ l1_struct_0(D_440)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_437),u1_struct_0(B_438))))
      | ~ v1_funct_2(C_439,u1_struct_0(A_437),u1_struct_0(B_438))
      | ~ v1_funct_1(C_439)
      | ~ l1_struct_0(B_438)
      | ~ l1_struct_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3445,plain,(
    ! [D_440] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_440),u1_struct_0(D_440),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_440)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3443])).

tff(c_3448,plain,(
    ! [D_440] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_440),u1_struct_0(D_440),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_440)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3445])).

tff(c_3460,plain,(
    ! [D_440] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_440),u1_struct_0(D_440),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_440)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3458,c_3448])).

tff(c_3461,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3460])).

tff(c_3464,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_3461])).

tff(c_3468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3464])).

tff(c_3470,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3460])).

tff(c_3475,plain,(
    ! [A_443,B_444,C_445,D_446] :
      ( m1_subset_1(k2_tmap_1(A_443,B_444,C_445,D_446),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_446),u1_struct_0(B_444))))
      | ~ l1_struct_0(D_446)
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_443),u1_struct_0(B_444))))
      | ~ v1_funct_2(C_445,u1_struct_0(A_443),u1_struct_0(B_444))
      | ~ v1_funct_1(C_445)
      | ~ l1_struct_0(B_444)
      | ~ l1_struct_0(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3252,plain,(
    ! [A_396,B_397,C_398,D_399] :
      ( v1_funct_1(k2_tmap_1(A_396,B_397,C_398,D_399))
      | ~ l1_struct_0(D_399)
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_396),u1_struct_0(B_397))))
      | ~ v1_funct_2(C_398,u1_struct_0(A_396),u1_struct_0(B_397))
      | ~ v1_funct_1(C_398)
      | ~ l1_struct_0(B_397)
      | ~ l1_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3256,plain,(
    ! [D_399] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_399))
      | ~ l1_struct_0(D_399)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3252])).

tff(c_3262,plain,(
    ! [D_399] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_399))
      | ~ l1_struct_0(D_399)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3256])).

tff(c_3274,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3262])).

tff(c_3277,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_3274])).

tff(c_3281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3277])).

tff(c_3283,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3262])).

tff(c_3263,plain,(
    ! [A_400,B_401,C_402,D_403] :
      ( v1_funct_2(k2_tmap_1(A_400,B_401,C_402,D_403),u1_struct_0(D_403),u1_struct_0(B_401))
      | ~ l1_struct_0(D_403)
      | ~ m1_subset_1(C_402,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_400),u1_struct_0(B_401))))
      | ~ v1_funct_2(C_402,u1_struct_0(A_400),u1_struct_0(B_401))
      | ~ v1_funct_1(C_402)
      | ~ l1_struct_0(B_401)
      | ~ l1_struct_0(A_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3267,plain,(
    ! [D_403] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_403),u1_struct_0(D_403),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_403)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3263])).

tff(c_3273,plain,(
    ! [D_403] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_403),u1_struct_0(D_403),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_403)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3267])).

tff(c_3285,plain,(
    ! [D_403] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_403),u1_struct_0(D_403),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_403)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3283,c_3273])).

tff(c_3286,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3285])).

tff(c_3289,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_3286])).

tff(c_3293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3289])).

tff(c_3295,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3285])).

tff(c_3344,plain,(
    ! [A_412,B_413,C_414,D_415] :
      ( m1_subset_1(k2_tmap_1(A_412,B_413,C_414,D_415),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_415),u1_struct_0(B_413))))
      | ~ l1_struct_0(D_415)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_412),u1_struct_0(B_413))))
      | ~ v1_funct_2(C_414,u1_struct_0(A_412),u1_struct_0(B_413))
      | ~ v1_funct_1(C_414)
      | ~ l1_struct_0(B_413)
      | ~ l1_struct_0(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_172,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_246,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_162,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_267,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_152,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_264,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_142,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_268,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_132,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_247,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_122,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_266,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_112,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_265,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_102,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_281,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_254])).

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

tff(c_365,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_267,c_264,c_268,c_247,c_266,c_265,c_281,c_206])).

tff(c_58,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_60,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_373,plain,(
    ! [A_131,B_132,C_133] :
      ( m1_pre_topc(k1_tsep_1(A_131,B_132,C_133),A_131)
      | ~ m1_pre_topc(C_133,A_131)
      | v2_struct_0(C_133)
      | ~ m1_pre_topc(B_132,A_131)
      | v2_struct_0(B_132)
      | ~ l1_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_379,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_373])).

tff(c_382,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_66,c_62,c_379])).

tff(c_383,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_68,c_64,c_382])).

tff(c_84,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_78,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_314,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k2_partfun1(A_118,B_119,C_120,D_121) = k7_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_320,plain,(
    ! [D_121] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_121) = k7_relat_1('#skF_3',D_121)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_70,c_314])).

tff(c_329,plain,(
    ! [D_121] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_121) = k7_relat_1('#skF_3',D_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_320])).

tff(c_594,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k2_partfun1(u1_struct_0(A_170),u1_struct_0(B_171),C_172,u1_struct_0(D_173)) = k2_tmap_1(A_170,B_171,C_172,D_173)
      | ~ m1_pre_topc(D_173,A_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_170),u1_struct_0(B_171))))
      | ~ v1_funct_2(C_172,u1_struct_0(A_170),u1_struct_0(B_171))
      | ~ v1_funct_1(C_172)
      | ~ l1_pre_topc(B_171)
      | ~ v2_pre_topc(B_171)
      | v2_struct_0(B_171)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_602,plain,(
    ! [D_173] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_173)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_173)
      | ~ m1_pre_topc(D_173,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_594])).

tff(c_614,plain,(
    ! [D_173] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_173)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_173)
      | ~ m1_pre_topc(D_173,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_78,c_76,c_74,c_72,c_329,c_602])).

tff(c_616,plain,(
    ! [D_174] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_174)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_174)
      | ~ m1_pre_topc(D_174,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_614])).

tff(c_8,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_229,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_8])).

tff(c_241,plain,(
    ! [C_111,A_112,B_113] :
      ( v4_relat_1(C_111,A_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_245,plain,(
    v4_relat_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_241])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_248,plain,(
    ! [B_114,A_115] :
      ( k7_relat_1(B_114,A_115) = B_114
      | ~ r1_tarski(k1_relat_1(B_114),A_115)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_253,plain,(
    ! [B_116,A_117] :
      ( k7_relat_1(B_116,A_117) = B_116
      | ~ v4_relat_1(B_116,A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_4,c_248])).

tff(c_256,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_245,c_253])).

tff(c_259,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_256])).

tff(c_622,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_259])).

tff(c_631,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_622])).

tff(c_2843,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2855,plain,(
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
    inference(resolution,[status(thm)],[c_281,c_2843])).

tff(c_2873,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_78,c_76,c_62,c_74,c_72,c_70,c_247,c_266,c_265,c_2855])).

tff(c_3144,plain,(
    ! [C_377] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_377,'#skF_5')),k1_tsep_1('#skF_1',C_377,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_377),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_377),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_377),C_377,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_377),u1_struct_0(C_377),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_377))
      | ~ r4_tsep_1('#skF_1',C_377,'#skF_5')
      | ~ m1_pre_topc(C_377,'#skF_1')
      | v2_struct_0(C_377) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_64,c_2873])).

tff(c_3157,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_268,c_3144])).

tff(c_3170,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_58,c_246,c_267,c_264,c_631,c_60,c_60,c_3157])).

tff(c_3172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_365,c_3170])).

tff(c_3174,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_3353,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3344,c_3174])).

tff(c_3368,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3283,c_3295,c_74,c_72,c_70,c_3353])).

tff(c_3374,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_3368])).

tff(c_3378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_3374])).

tff(c_3380,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_3484,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3475,c_3380])).

tff(c_3499,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3458,c_3470,c_74,c_72,c_70,c_3484])).

tff(c_3515,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_3499])).

tff(c_3519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_3515])).

tff(c_3521,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_3617,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3613,c_3521])).

tff(c_3620,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_3617])).

tff(c_3624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_3620])).

tff(c_3626,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_3722,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3718,c_3626])).

tff(c_3747,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_3722])).

tff(c_3751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_3747])).

tff(c_3753,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_3811,plain,(
    ! [A_525,B_526,C_527,D_528] :
      ( v1_funct_1(k2_tmap_1(A_525,B_526,C_527,D_528))
      | ~ l1_struct_0(D_528)
      | ~ m1_subset_1(C_527,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_525),u1_struct_0(B_526))))
      | ~ v1_funct_2(C_527,u1_struct_0(A_525),u1_struct_0(B_526))
      | ~ v1_funct_1(C_527)
      | ~ l1_struct_0(B_526)
      | ~ l1_struct_0(A_525) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3813,plain,(
    ! [D_528] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_528))
      | ~ l1_struct_0(D_528)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3811])).

tff(c_3816,plain,(
    ! [D_528] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_528))
      | ~ l1_struct_0(D_528)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3813])).

tff(c_3817,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3816])).

tff(c_3820,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_3817])).

tff(c_3824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3820])).

tff(c_3826,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3816])).

tff(c_3787,plain,(
    ! [A_519,B_520,C_521] :
      ( m1_pre_topc(k1_tsep_1(A_519,B_520,C_521),A_519)
      | ~ m1_pre_topc(C_521,A_519)
      | v2_struct_0(C_521)
      | ~ m1_pre_topc(B_520,A_519)
      | v2_struct_0(B_520)
      | ~ l1_pre_topc(A_519)
      | v2_struct_0(A_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3793,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_3787])).

tff(c_3796,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_66,c_62,c_3793])).

tff(c_3797,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_68,c_64,c_3796])).

tff(c_3758,plain,(
    ! [A_508,B_509,C_510,D_511] :
      ( k2_partfun1(A_508,B_509,C_510,D_511) = k7_relat_1(C_510,D_511)
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k2_zfmisc_1(A_508,B_509)))
      | ~ v1_funct_1(C_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3760,plain,(
    ! [D_511] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_511) = k7_relat_1('#skF_3',D_511)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_70,c_3758])).

tff(c_3763,plain,(
    ! [D_511] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_511) = k7_relat_1('#skF_3',D_511) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3760])).

tff(c_3888,plain,(
    ! [A_548,B_549,C_550,D_551] :
      ( k2_partfun1(u1_struct_0(A_548),u1_struct_0(B_549),C_550,u1_struct_0(D_551)) = k2_tmap_1(A_548,B_549,C_550,D_551)
      | ~ m1_pre_topc(D_551,A_548)
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_548),u1_struct_0(B_549))))
      | ~ v1_funct_2(C_550,u1_struct_0(A_548),u1_struct_0(B_549))
      | ~ v1_funct_1(C_550)
      | ~ l1_pre_topc(B_549)
      | ~ v2_pre_topc(B_549)
      | v2_struct_0(B_549)
      | ~ l1_pre_topc(A_548)
      | ~ v2_pre_topc(A_548)
      | v2_struct_0(A_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3892,plain,(
    ! [D_551] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_551)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_551)
      | ~ m1_pre_topc(D_551,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3888])).

tff(c_3896,plain,(
    ! [D_551] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_551)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_551)
      | ~ m1_pre_topc(D_551,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_78,c_76,c_74,c_72,c_3763,c_3892])).

tff(c_3903,plain,(
    ! [D_553] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_553)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_553)
      | ~ m1_pre_topc(D_553,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_3896])).

tff(c_3909,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3903,c_259])).

tff(c_3918,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3797,c_3909])).

tff(c_3752,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_3825,plain,(
    ! [D_528] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_528))
      | ~ l1_struct_0(D_528) ) ),
    inference(splitRight,[status(thm)],[c_3816])).

tff(c_3833,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3825])).

tff(c_3836,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_3833])).

tff(c_3840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3836])).

tff(c_3841,plain,(
    ! [D_528] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_528))
      | ~ l1_struct_0(D_528) ) ),
    inference(splitRight,[status(thm)],[c_3825])).

tff(c_3842,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3825])).

tff(c_3847,plain,(
    ! [A_535,B_536,C_537,D_538] :
      ( m1_subset_1(k2_tmap_1(A_535,B_536,C_537,D_538),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_538),u1_struct_0(B_536))))
      | ~ l1_struct_0(D_538)
      | ~ m1_subset_1(C_537,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_535),u1_struct_0(B_536))))
      | ~ v1_funct_2(C_537,u1_struct_0(A_535),u1_struct_0(B_536))
      | ~ v1_funct_1(C_537)
      | ~ l1_struct_0(B_536)
      | ~ l1_struct_0(A_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3869,plain,(
    ! [A_539,B_540,C_541,D_542] :
      ( v1_relat_1(k2_tmap_1(A_539,B_540,C_541,D_542))
      | ~ l1_struct_0(D_542)
      | ~ m1_subset_1(C_541,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_539),u1_struct_0(B_540))))
      | ~ v1_funct_2(C_541,u1_struct_0(A_539),u1_struct_0(B_540))
      | ~ v1_funct_1(C_541)
      | ~ l1_struct_0(B_540)
      | ~ l1_struct_0(A_539) ) ),
    inference(resolution,[status(thm)],[c_3847,c_8])).

tff(c_3873,plain,(
    ! [D_542] :
      ( v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_542))
      | ~ l1_struct_0(D_542)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3869])).

tff(c_3877,plain,(
    ! [D_542] :
      ( v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_542))
      | ~ l1_struct_0(D_542) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3826,c_3842,c_74,c_72,c_3873])).

tff(c_3827,plain,(
    ! [A_529,B_530,C_531,D_532] :
      ( v1_funct_2(k2_tmap_1(A_529,B_530,C_531,D_532),u1_struct_0(D_532),u1_struct_0(B_530))
      | ~ l1_struct_0(D_532)
      | ~ m1_subset_1(C_531,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_529),u1_struct_0(B_530))))
      | ~ v1_funct_2(C_531,u1_struct_0(A_529),u1_struct_0(B_530))
      | ~ v1_funct_1(C_531)
      | ~ l1_struct_0(B_530)
      | ~ l1_struct_0(A_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3829,plain,(
    ! [D_532] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_532),u1_struct_0(D_532),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_532)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3827])).

tff(c_3832,plain,(
    ! [D_532] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_532),u1_struct_0(D_532),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_532)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3826,c_74,c_72,c_3829])).

tff(c_3844,plain,(
    ! [D_532] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_532),u1_struct_0(D_532),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_532) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3842,c_3832])).

tff(c_28,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( m1_subset_1(k2_tmap_1(A_37,B_38,C_39,D_40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_40),u1_struct_0(B_38))))
      | ~ l1_struct_0(D_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_37),u1_struct_0(B_38))))
      | ~ v1_funct_2(C_39,u1_struct_0(A_37),u1_struct_0(B_38))
      | ~ v1_funct_1(C_39)
      | ~ l1_struct_0(B_38)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4157,plain,(
    ! [C_615,A_611,B_612,D_614,D_613] :
      ( k2_partfun1(u1_struct_0(D_613),u1_struct_0(B_612),k2_tmap_1(A_611,B_612,C_615,D_613),u1_struct_0(D_614)) = k2_tmap_1(D_613,B_612,k2_tmap_1(A_611,B_612,C_615,D_613),D_614)
      | ~ m1_pre_topc(D_614,D_613)
      | ~ v1_funct_2(k2_tmap_1(A_611,B_612,C_615,D_613),u1_struct_0(D_613),u1_struct_0(B_612))
      | ~ v1_funct_1(k2_tmap_1(A_611,B_612,C_615,D_613))
      | ~ l1_pre_topc(B_612)
      | ~ v2_pre_topc(B_612)
      | v2_struct_0(B_612)
      | ~ l1_pre_topc(D_613)
      | ~ v2_pre_topc(D_613)
      | v2_struct_0(D_613)
      | ~ l1_struct_0(D_613)
      | ~ m1_subset_1(C_615,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_611),u1_struct_0(B_612))))
      | ~ v1_funct_2(C_615,u1_struct_0(A_611),u1_struct_0(B_612))
      | ~ v1_funct_1(C_615)
      | ~ l1_struct_0(B_612)
      | ~ l1_struct_0(A_611) ) ),
    inference(resolution,[status(thm)],[c_28,c_3888])).

tff(c_4161,plain,(
    ! [D_613,D_614] :
      ( k2_partfun1(u1_struct_0(D_613),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_613),u1_struct_0(D_614)) = k2_tmap_1(D_613,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_613),D_614)
      | ~ m1_pre_topc(D_614,D_613)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_613),u1_struct_0(D_613),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_613))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(D_613)
      | ~ v2_pre_topc(D_613)
      | v2_struct_0(D_613)
      | ~ l1_struct_0(D_613)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_4157])).

tff(c_4165,plain,(
    ! [D_613,D_614] :
      ( k2_partfun1(u1_struct_0(D_613),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_613),u1_struct_0(D_614)) = k2_tmap_1(D_613,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_613),D_614)
      | ~ m1_pre_topc(D_614,D_613)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_613),u1_struct_0(D_613),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_613))
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(D_613)
      | ~ v2_pre_topc(D_613)
      | v2_struct_0(D_613)
      | ~ l1_struct_0(D_613) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3826,c_3842,c_74,c_72,c_78,c_76,c_4161])).

tff(c_4167,plain,(
    ! [D_616,D_617] :
      ( k2_partfun1(u1_struct_0(D_616),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_616),u1_struct_0(D_617)) = k2_tmap_1(D_616,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_616),D_617)
      | ~ m1_pre_topc(D_617,D_616)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_616),u1_struct_0(D_616),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_616))
      | ~ l1_pre_topc(D_616)
      | ~ v2_pre_topc(D_616)
      | v2_struct_0(D_616)
      | ~ l1_struct_0(D_616) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_4165])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k2_partfun1(A_11,B_12,C_13,D_14) = k7_relat_1(C_13,D_14)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3981,plain,(
    ! [A_562,D_561,D_563,C_564,B_560] :
      ( k2_partfun1(u1_struct_0(D_561),u1_struct_0(B_560),k2_tmap_1(A_562,B_560,C_564,D_561),D_563) = k7_relat_1(k2_tmap_1(A_562,B_560,C_564,D_561),D_563)
      | ~ v1_funct_1(k2_tmap_1(A_562,B_560,C_564,D_561))
      | ~ l1_struct_0(D_561)
      | ~ m1_subset_1(C_564,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_562),u1_struct_0(B_560))))
      | ~ v1_funct_2(C_564,u1_struct_0(A_562),u1_struct_0(B_560))
      | ~ v1_funct_1(C_564)
      | ~ l1_struct_0(B_560)
      | ~ l1_struct_0(A_562) ) ),
    inference(resolution,[status(thm)],[c_3847,c_14])).

tff(c_3985,plain,(
    ! [D_561,D_563] :
      ( k2_partfun1(u1_struct_0(D_561),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_561),D_563) = k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_561),D_563)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_561))
      | ~ l1_struct_0(D_561)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3981])).

tff(c_3989,plain,(
    ! [D_561,D_563] :
      ( k2_partfun1(u1_struct_0(D_561),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_561),D_563) = k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_561),D_563)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_561))
      | ~ l1_struct_0(D_561) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3826,c_3842,c_74,c_72,c_3985])).

tff(c_4189,plain,(
    ! [D_618,D_619] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_618),u1_struct_0(D_619)) = k2_tmap_1(D_618,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_618),D_619)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_618))
      | ~ l1_struct_0(D_618)
      | ~ m1_pre_topc(D_619,D_618)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_618),u1_struct_0(D_618),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_618))
      | ~ l1_pre_topc(D_618)
      | ~ v2_pre_topc(D_618)
      | v2_struct_0(D_618)
      | ~ l1_struct_0(D_618) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4167,c_3989])).

tff(c_4198,plain,(
    ! [D_620,D_621] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_620),u1_struct_0(D_621)) = k2_tmap_1(D_620,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_620),D_621)
      | ~ m1_pre_topc(D_621,D_620)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_620))
      | ~ l1_pre_topc(D_620)
      | ~ v2_pre_topc(D_620)
      | v2_struct_0(D_620)
      | ~ l1_struct_0(D_620) ) ),
    inference(resolution,[status(thm)],[c_3844,c_4189])).

tff(c_12,plain,(
    ! [C_10,A_8,B_9] :
      ( v4_relat_1(C_10,A_8)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3879,plain,(
    ! [A_544,B_545,C_546,D_547] :
      ( v4_relat_1(k2_tmap_1(A_544,B_545,C_546,D_547),u1_struct_0(D_547))
      | ~ l1_struct_0(D_547)
      | ~ m1_subset_1(C_546,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_544),u1_struct_0(B_545))))
      | ~ v1_funct_2(C_546,u1_struct_0(A_544),u1_struct_0(B_545))
      | ~ v1_funct_1(C_546)
      | ~ l1_struct_0(B_545)
      | ~ l1_struct_0(A_544) ) ),
    inference(resolution,[status(thm)],[c_3847,c_12])).

tff(c_3883,plain,(
    ! [D_547] :
      ( v4_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_547),u1_struct_0(D_547))
      | ~ l1_struct_0(D_547)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_3879])).

tff(c_3898,plain,(
    ! [D_552] :
      ( v4_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_552),u1_struct_0(D_552))
      | ~ l1_struct_0(D_552) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3826,c_3842,c_74,c_72,c_3883])).

tff(c_252,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_248])).

tff(c_3902,plain,(
    ! [D_552] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_552),u1_struct_0(D_552)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_552)
      | ~ v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_552))
      | ~ l1_struct_0(D_552) ) ),
    inference(resolution,[status(thm)],[c_3898,c_252])).

tff(c_4696,plain,(
    ! [D_662] :
      ( k2_tmap_1(D_662,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_662),D_662) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_662)
      | ~ v1_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_662))
      | ~ l1_struct_0(D_662)
      | ~ m1_pre_topc(D_662,D_662)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_662))
      | ~ l1_pre_topc(D_662)
      | ~ v2_pre_topc(D_662)
      | v2_struct_0(D_662)
      | ~ l1_struct_0(D_662) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4198,c_3902])).

tff(c_4705,plain,(
    ! [D_663] :
      ( k2_tmap_1(D_663,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_663),D_663) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_663)
      | ~ m1_pre_topc(D_663,D_663)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_663))
      | ~ l1_pre_topc(D_663)
      | ~ v2_pre_topc(D_663)
      | v2_struct_0(D_663)
      | ~ l1_struct_0(D_663) ) ),
    inference(resolution,[status(thm)],[c_3877,c_4696])).

tff(c_4717,plain,(
    ! [D_528] :
      ( k2_tmap_1(D_528,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_528),D_528) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_528)
      | ~ m1_pre_topc(D_528,D_528)
      | ~ l1_pre_topc(D_528)
      | ~ v2_pre_topc(D_528)
      | v2_struct_0(D_528)
      | ~ l1_struct_0(D_528) ) ),
    inference(resolution,[status(thm)],[c_3841,c_4705])).

tff(c_4662,plain,(
    ! [A_656,D_660,C_659,E_657,B_658] :
      ( v5_pre_topc(k2_tmap_1(A_656,B_658,E_657,D_660),D_660,B_658)
      | ~ m1_subset_1(k2_tmap_1(A_656,B_658,E_657,k1_tsep_1(A_656,C_659,D_660)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_656,C_659,D_660)),u1_struct_0(B_658))))
      | ~ v5_pre_topc(k2_tmap_1(A_656,B_658,E_657,k1_tsep_1(A_656,C_659,D_660)),k1_tsep_1(A_656,C_659,D_660),B_658)
      | ~ v1_funct_2(k2_tmap_1(A_656,B_658,E_657,k1_tsep_1(A_656,C_659,D_660)),u1_struct_0(k1_tsep_1(A_656,C_659,D_660)),u1_struct_0(B_658))
      | ~ v1_funct_1(k2_tmap_1(A_656,B_658,E_657,k1_tsep_1(A_656,C_659,D_660)))
      | ~ m1_subset_1(E_657,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_656),u1_struct_0(B_658))))
      | ~ v1_funct_2(E_657,u1_struct_0(A_656),u1_struct_0(B_658))
      | ~ v1_funct_1(E_657)
      | ~ r4_tsep_1(A_656,C_659,D_660)
      | ~ m1_pre_topc(D_660,A_656)
      | v2_struct_0(D_660)
      | ~ m1_pre_topc(C_659,A_656)
      | v2_struct_0(C_659)
      | ~ l1_pre_topc(B_658)
      | ~ v2_pre_topc(B_658)
      | v2_struct_0(B_658)
      | ~ l1_pre_topc(A_656)
      | ~ v2_pre_topc(A_656)
      | v2_struct_0(A_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_4673,plain,(
    ! [B_658,E_657] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_658,E_657,'#skF_5'),'#skF_5',B_658)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_658,E_657,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_658))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_658,E_657,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_658)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_658,E_657,k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_658))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_658,E_657,k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_657,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_658))))
      | ~ v1_funct_2(E_657,u1_struct_0('#skF_1'),u1_struct_0(B_658))
      | ~ v1_funct_1(E_657)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_658)
      | ~ v2_pre_topc(B_658)
      | v2_struct_0(B_658)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_4662])).

tff(c_4682,plain,(
    ! [B_658,E_657] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_658,E_657,'#skF_5'),'#skF_5',B_658)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_658,E_657,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_658))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_658,E_657,'#skF_1'),'#skF_1',B_658)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_658,E_657,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_658))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_658,E_657,'#skF_1'))
      | ~ m1_subset_1(E_657,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_658))))
      | ~ v1_funct_2(E_657,u1_struct_0('#skF_1'),u1_struct_0(B_658))
      | ~ v1_funct_1(E_657)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_658)
      | ~ v2_pre_topc(B_658)
      | v2_struct_0(B_658)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_66,c_62,c_58,c_60,c_60,c_60,c_60,c_60,c_60,c_4673])).

tff(c_5257,plain,(
    ! [B_693,E_694] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_693,E_694,'#skF_5'),'#skF_5',B_693)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_693,E_694,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_693))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_693,E_694,'#skF_1'),'#skF_1',B_693)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_693,E_694,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_693))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_693,E_694,'#skF_1'))
      | ~ m1_subset_1(E_694,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_693))))
      | ~ v1_funct_2(E_694,u1_struct_0('#skF_1'),u1_struct_0(B_693))
      | ~ v1_funct_1(E_694)
      | ~ l1_pre_topc(B_693)
      | ~ v2_pre_topc(B_693)
      | v2_struct_0(B_693) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_68,c_64,c_4682])).

tff(c_5261,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),'#skF_5'),'#skF_5','#skF_2')
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
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
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4717,c_5257])).

tff(c_5274,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3826,c_84,c_82,c_3797,c_78,c_76,c_74,c_3918,c_72,c_3918,c_70,c_3918,c_74,c_3918,c_3918,c_72,c_3918,c_3918,c_3752,c_3918,c_3918,c_70,c_3918,c_3918,c_5261])).

tff(c_5276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_3753,c_5274])).

tff(c_5278,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_5315,plain,(
    ! [A_706,B_707,C_708] :
      ( m1_pre_topc(k1_tsep_1(A_706,B_707,C_708),A_706)
      | ~ m1_pre_topc(C_708,A_706)
      | v2_struct_0(C_708)
      | ~ m1_pre_topc(B_707,A_706)
      | v2_struct_0(B_707)
      | ~ l1_pre_topc(A_706)
      | v2_struct_0(A_706) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5321,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_5315])).

tff(c_5324,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_66,c_62,c_5321])).

tff(c_5325,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_68,c_64,c_5324])).

tff(c_5283,plain,(
    ! [A_695,B_696,C_697,D_698] :
      ( k2_partfun1(A_695,B_696,C_697,D_698) = k7_relat_1(C_697,D_698)
      | ~ m1_subset_1(C_697,k1_zfmisc_1(k2_zfmisc_1(A_695,B_696)))
      | ~ v1_funct_1(C_697) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5285,plain,(
    ! [D_698] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_698) = k7_relat_1('#skF_3',D_698)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_70,c_5283])).

tff(c_5288,plain,(
    ! [D_698] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_698) = k7_relat_1('#skF_3',D_698) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5285])).

tff(c_5405,plain,(
    ! [A_731,B_732,C_733,D_734] :
      ( k2_partfun1(u1_struct_0(A_731),u1_struct_0(B_732),C_733,u1_struct_0(D_734)) = k2_tmap_1(A_731,B_732,C_733,D_734)
      | ~ m1_pre_topc(D_734,A_731)
      | ~ m1_subset_1(C_733,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_731),u1_struct_0(B_732))))
      | ~ v1_funct_2(C_733,u1_struct_0(A_731),u1_struct_0(B_732))
      | ~ v1_funct_1(C_733)
      | ~ l1_pre_topc(B_732)
      | ~ v2_pre_topc(B_732)
      | v2_struct_0(B_732)
      | ~ l1_pre_topc(A_731)
      | ~ v2_pre_topc(A_731)
      | v2_struct_0(A_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5409,plain,(
    ! [D_734] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_734)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_734)
      | ~ m1_pre_topc(D_734,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_5405])).

tff(c_5413,plain,(
    ! [D_734] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_734)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_734)
      | ~ m1_pre_topc(D_734,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_78,c_76,c_74,c_72,c_5288,c_5409])).

tff(c_5415,plain,(
    ! [D_735] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_735)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_735)
      | ~ m1_pre_topc(D_735,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_5413])).

tff(c_5421,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5415,c_259])).

tff(c_5430,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5325,c_5421])).

tff(c_5277,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_5815,plain,(
    ! [E_824,D_827,A_823,C_826,B_825] :
      ( v5_pre_topc(k2_tmap_1(A_823,B_825,E_824,C_826),C_826,B_825)
      | ~ m1_subset_1(k2_tmap_1(A_823,B_825,E_824,k1_tsep_1(A_823,C_826,D_827)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_823,C_826,D_827)),u1_struct_0(B_825))))
      | ~ v5_pre_topc(k2_tmap_1(A_823,B_825,E_824,k1_tsep_1(A_823,C_826,D_827)),k1_tsep_1(A_823,C_826,D_827),B_825)
      | ~ v1_funct_2(k2_tmap_1(A_823,B_825,E_824,k1_tsep_1(A_823,C_826,D_827)),u1_struct_0(k1_tsep_1(A_823,C_826,D_827)),u1_struct_0(B_825))
      | ~ v1_funct_1(k2_tmap_1(A_823,B_825,E_824,k1_tsep_1(A_823,C_826,D_827)))
      | ~ m1_subset_1(E_824,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_823),u1_struct_0(B_825))))
      | ~ v1_funct_2(E_824,u1_struct_0(A_823),u1_struct_0(B_825))
      | ~ v1_funct_1(E_824)
      | ~ r4_tsep_1(A_823,C_826,D_827)
      | ~ m1_pre_topc(D_827,A_823)
      | v2_struct_0(D_827)
      | ~ m1_pre_topc(C_826,A_823)
      | v2_struct_0(C_826)
      | ~ l1_pre_topc(B_825)
      | ~ v2_pre_topc(B_825)
      | v2_struct_0(B_825)
      | ~ l1_pre_topc(A_823)
      | ~ v2_pre_topc(A_823)
      | v2_struct_0(A_823) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_5822,plain,(
    ! [B_825,E_824] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_825,E_824,'#skF_4'),'#skF_4',B_825)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_825,E_824,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_825))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_825,E_824,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_825)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_825,E_824,k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_825))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_825,E_824,k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_824,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_825))))
      | ~ v1_funct_2(E_824,u1_struct_0('#skF_1'),u1_struct_0(B_825))
      | ~ v1_funct_1(E_824)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_825)
      | ~ v2_pre_topc(B_825)
      | v2_struct_0(B_825)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_5815])).

tff(c_5828,plain,(
    ! [B_825,E_824] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_825,E_824,'#skF_4'),'#skF_4',B_825)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_825,E_824,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_825))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_825,E_824,'#skF_1'),'#skF_1',B_825)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_825,E_824,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_825))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_825,E_824,'#skF_1'))
      | ~ m1_subset_1(E_824,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_825))))
      | ~ v1_funct_2(E_824,u1_struct_0('#skF_1'),u1_struct_0(B_825))
      | ~ v1_funct_1(E_824)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_825)
      | ~ v2_pre_topc(B_825)
      | v2_struct_0(B_825)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_66,c_62,c_58,c_60,c_60,c_60,c_60,c_60,c_60,c_5822])).

tff(c_6094,plain,(
    ! [B_851,E_852] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_851,E_852,'#skF_4'),'#skF_4',B_851)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_851,E_852,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_851))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_851,E_852,'#skF_1'),'#skF_1',B_851)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_851,E_852,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_851))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_851,E_852,'#skF_1'))
      | ~ m1_subset_1(E_852,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_851))))
      | ~ v1_funct_2(E_852,u1_struct_0('#skF_1'),u1_struct_0(B_851))
      | ~ v1_funct_1(E_852)
      | ~ l1_pre_topc(B_851)
      | ~ v2_pre_topc(B_851)
      | v2_struct_0(B_851) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_68,c_64,c_5828])).

tff(c_6097,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_5430,c_6094])).

tff(c_6103,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_74,c_5430,c_72,c_5430,c_5277,c_5430,c_70,c_6097])).

tff(c_6105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_5278,c_6103])).

tff(c_6107,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_6221,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6217,c_6107])).

tff(c_6224,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_6221])).

tff(c_6228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_6224])).

tff(c_6230,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_6348,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6344,c_6230])).

tff(c_6351,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_6348])).

tff(c_6355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_6351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.78/3.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.00/3.06  
% 9.00/3.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.00/3.06  %$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.00/3.06  
% 9.00/3.06  %Foreground sorts:
% 9.00/3.06  
% 9.00/3.06  
% 9.00/3.06  %Background operators:
% 9.00/3.06  
% 9.00/3.06  
% 9.00/3.06  %Foreground operators:
% 9.00/3.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.00/3.06  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 9.00/3.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.00/3.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.00/3.06  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.00/3.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.00/3.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.00/3.06  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 9.00/3.06  tff('#skF_5', type, '#skF_5': $i).
% 9.00/3.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.00/3.06  tff('#skF_2', type, '#skF_2': $i).
% 9.00/3.06  tff('#skF_3', type, '#skF_3': $i).
% 9.00/3.06  tff('#skF_1', type, '#skF_1': $i).
% 9.00/3.06  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.00/3.06  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.00/3.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.00/3.06  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.00/3.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.00/3.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.00/3.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.00/3.06  tff('#skF_4', type, '#skF_4': $i).
% 9.00/3.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.00/3.06  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 9.00/3.06  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.00/3.06  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.00/3.06  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.00/3.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.00/3.06  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 9.00/3.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.00/3.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.00/3.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.00/3.06  
% 9.30/3.10  tff(f_254, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (((A = k1_tsep_1(A, D, E)) & r4_tsep_1(A, D, E)) => ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, C, E))) & v1_funct_2(k2_tmap_1(A, B, C, E), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, E), E, B)) & m1_subset_1(k2_tmap_1(A, B, C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_tmap_1)).
% 9.30/3.10  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.30/3.10  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.30/3.10  tff(f_131, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 9.30/3.10  tff(f_113, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 9.30/3.10  tff(f_53, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.30/3.10  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 9.30/3.10  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.30/3.10  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.30/3.10  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.30/3.10  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 9.30/3.10  tff(f_191, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_funct_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D))) & v1_funct_2(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_tsep_1(A, C, D), B)) & m1_subset_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, E, C)) & v1_funct_2(k2_tmap_1(A, B, E, C), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, C), C, B)) & m1_subset_1(k2_tmap_1(A, B, E, C), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, E, D))) & v1_funct_2(k2_tmap_1(A, B, E, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, E, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_tmap_1)).
% 9.30/3.10  tff(c_82, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_66, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_212, plain, (![B_99, A_100]: (l1_pre_topc(B_99) | ~m1_pre_topc(B_99, A_100) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.30/3.10  tff(c_215, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_212])).
% 9.30/3.10  tff(c_221, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_215])).
% 9.30/3.10  tff(c_16, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.30/3.10  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_72, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_6309, plain, (![A_904, B_905, C_906, D_907]: (v1_funct_1(k2_tmap_1(A_904, B_905, C_906, D_907)) | ~l1_struct_0(D_907) | ~m1_subset_1(C_906, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_904), u1_struct_0(B_905)))) | ~v1_funct_2(C_906, u1_struct_0(A_904), u1_struct_0(B_905)) | ~v1_funct_1(C_906) | ~l1_struct_0(B_905) | ~l1_struct_0(A_904))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_6311, plain, (![D_907]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_907)) | ~l1_struct_0(D_907) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_6309])).
% 9.30/3.10  tff(c_6314, plain, (![D_907]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_907)) | ~l1_struct_0(D_907) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_6311])).
% 9.30/3.10  tff(c_6315, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_6314])).
% 9.30/3.10  tff(c_6318, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_6315])).
% 9.30/3.10  tff(c_6322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_6318])).
% 9.30/3.10  tff(c_6323, plain, (![D_907]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_907)) | ~l1_struct_0(D_907))), inference(splitRight, [status(thm)], [c_6314])).
% 9.30/3.10  tff(c_6331, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_6323])).
% 9.30/3.10  tff(c_6334, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_6331])).
% 9.30/3.10  tff(c_6338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_6334])).
% 9.30/3.10  tff(c_6344, plain, (![D_913]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_913)) | ~l1_struct_0(D_913))), inference(splitRight, [status(thm)], [c_6323])).
% 9.30/3.10  tff(c_62, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_218, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_212])).
% 9.30/3.10  tff(c_224, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_218])).
% 9.30/3.10  tff(c_6185, plain, (![A_874, B_875, C_876, D_877]: (v1_funct_1(k2_tmap_1(A_874, B_875, C_876, D_877)) | ~l1_struct_0(D_877) | ~m1_subset_1(C_876, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_874), u1_struct_0(B_875)))) | ~v1_funct_2(C_876, u1_struct_0(A_874), u1_struct_0(B_875)) | ~v1_funct_1(C_876) | ~l1_struct_0(B_875) | ~l1_struct_0(A_874))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_6187, plain, (![D_877]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_877)) | ~l1_struct_0(D_877) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_6185])).
% 9.30/3.10  tff(c_6190, plain, (![D_877]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_877)) | ~l1_struct_0(D_877) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_6187])).
% 9.30/3.10  tff(c_6191, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_6190])).
% 9.30/3.10  tff(c_6194, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_6191])).
% 9.30/3.10  tff(c_6198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_6194])).
% 9.30/3.10  tff(c_6199, plain, (![D_877]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_877)) | ~l1_struct_0(D_877))), inference(splitRight, [status(thm)], [c_6190])).
% 9.30/3.10  tff(c_6201, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_6199])).
% 9.30/3.10  tff(c_6210, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_6201])).
% 9.30/3.10  tff(c_6214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_6210])).
% 9.30/3.10  tff(c_6217, plain, (![D_882]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_882)) | ~l1_struct_0(D_882))), inference(splitRight, [status(thm)], [c_6199])).
% 9.30/3.10  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_86, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_3685, plain, (![A_494, B_495, C_496, D_497]: (v1_funct_1(k2_tmap_1(A_494, B_495, C_496, D_497)) | ~l1_struct_0(D_497) | ~m1_subset_1(C_496, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_494), u1_struct_0(B_495)))) | ~v1_funct_2(C_496, u1_struct_0(A_494), u1_struct_0(B_495)) | ~v1_funct_1(C_496) | ~l1_struct_0(B_495) | ~l1_struct_0(A_494))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_3687, plain, (![D_497]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_497)) | ~l1_struct_0(D_497) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3685])).
% 9.30/3.10  tff(c_3690, plain, (![D_497]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_497)) | ~l1_struct_0(D_497) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3687])).
% 9.30/3.10  tff(c_3691, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3690])).
% 9.30/3.10  tff(c_3694, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_3691])).
% 9.30/3.10  tff(c_3698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_3694])).
% 9.30/3.10  tff(c_3700, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3690])).
% 9.30/3.10  tff(c_3699, plain, (![D_497]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_497)) | ~l1_struct_0(D_497))), inference(splitRight, [status(thm)], [c_3690])).
% 9.30/3.10  tff(c_3701, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3699])).
% 9.30/3.10  tff(c_3704, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_3701])).
% 9.30/3.10  tff(c_3708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_3704])).
% 9.30/3.10  tff(c_3710, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3699])).
% 9.30/3.10  tff(c_3712, plain, (![A_499, B_500, C_501, D_502]: (v1_funct_2(k2_tmap_1(A_499, B_500, C_501, D_502), u1_struct_0(D_502), u1_struct_0(B_500)) | ~l1_struct_0(D_502) | ~m1_subset_1(C_501, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_499), u1_struct_0(B_500)))) | ~v1_funct_2(C_501, u1_struct_0(A_499), u1_struct_0(B_500)) | ~v1_funct_1(C_501) | ~l1_struct_0(B_500) | ~l1_struct_0(A_499))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_3714, plain, (![D_502]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_502), u1_struct_0(D_502), u1_struct_0('#skF_2')) | ~l1_struct_0(D_502) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3712])).
% 9.30/3.10  tff(c_3718, plain, (![D_503]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_503), u1_struct_0(D_503), u1_struct_0('#skF_2')) | ~l1_struct_0(D_503))), inference(demodulation, [status(thm), theory('equality')], [c_3700, c_3710, c_74, c_72, c_3714])).
% 9.30/3.10  tff(c_3579, plain, (![A_468, B_469, C_470, D_471]: (v1_funct_1(k2_tmap_1(A_468, B_469, C_470, D_471)) | ~l1_struct_0(D_471) | ~m1_subset_1(C_470, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_468), u1_struct_0(B_469)))) | ~v1_funct_2(C_470, u1_struct_0(A_468), u1_struct_0(B_469)) | ~v1_funct_1(C_470) | ~l1_struct_0(B_469) | ~l1_struct_0(A_468))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_3581, plain, (![D_471]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_471)) | ~l1_struct_0(D_471) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3579])).
% 9.30/3.10  tff(c_3584, plain, (![D_471]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_471)) | ~l1_struct_0(D_471) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3581])).
% 9.30/3.10  tff(c_3585, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3584])).
% 9.30/3.10  tff(c_3588, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_3585])).
% 9.30/3.10  tff(c_3592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_3588])).
% 9.30/3.10  tff(c_3593, plain, (![D_471]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_471)) | ~l1_struct_0(D_471))), inference(splitRight, [status(thm)], [c_3584])).
% 9.30/3.10  tff(c_3601, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3593])).
% 9.30/3.10  tff(c_3604, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_3601])).
% 9.30/3.10  tff(c_3608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_3604])).
% 9.30/3.10  tff(c_3610, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3593])).
% 9.30/3.10  tff(c_3594, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3584])).
% 9.30/3.10  tff(c_3595, plain, (![A_472, B_473, C_474, D_475]: (v1_funct_2(k2_tmap_1(A_472, B_473, C_474, D_475), u1_struct_0(D_475), u1_struct_0(B_473)) | ~l1_struct_0(D_475) | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_472), u1_struct_0(B_473)))) | ~v1_funct_2(C_474, u1_struct_0(A_472), u1_struct_0(B_473)) | ~v1_funct_1(C_474) | ~l1_struct_0(B_473) | ~l1_struct_0(A_472))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_3597, plain, (![D_475]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_475), u1_struct_0(D_475), u1_struct_0('#skF_2')) | ~l1_struct_0(D_475) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3595])).
% 9.30/3.10  tff(c_3600, plain, (![D_475]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_475), u1_struct_0(D_475), u1_struct_0('#skF_2')) | ~l1_struct_0(D_475) | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3594, c_74, c_72, c_3597])).
% 9.30/3.10  tff(c_3613, plain, (![D_476]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_476), u1_struct_0(D_476), u1_struct_0('#skF_2')) | ~l1_struct_0(D_476))), inference(demodulation, [status(thm), theory('equality')], [c_3610, c_3600])).
% 9.30/3.10  tff(c_3437, plain, (![A_433, B_434, C_435, D_436]: (v1_funct_1(k2_tmap_1(A_433, B_434, C_435, D_436)) | ~l1_struct_0(D_436) | ~m1_subset_1(C_435, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_433), u1_struct_0(B_434)))) | ~v1_funct_2(C_435, u1_struct_0(A_433), u1_struct_0(B_434)) | ~v1_funct_1(C_435) | ~l1_struct_0(B_434) | ~l1_struct_0(A_433))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_3439, plain, (![D_436]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_436)) | ~l1_struct_0(D_436) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3437])).
% 9.30/3.10  tff(c_3442, plain, (![D_436]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_436)) | ~l1_struct_0(D_436) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3439])).
% 9.30/3.10  tff(c_3449, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3442])).
% 9.30/3.10  tff(c_3452, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_3449])).
% 9.30/3.10  tff(c_3456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_3452])).
% 9.30/3.10  tff(c_3458, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3442])).
% 9.30/3.10  tff(c_3443, plain, (![A_437, B_438, C_439, D_440]: (v1_funct_2(k2_tmap_1(A_437, B_438, C_439, D_440), u1_struct_0(D_440), u1_struct_0(B_438)) | ~l1_struct_0(D_440) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_437), u1_struct_0(B_438)))) | ~v1_funct_2(C_439, u1_struct_0(A_437), u1_struct_0(B_438)) | ~v1_funct_1(C_439) | ~l1_struct_0(B_438) | ~l1_struct_0(A_437))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_3445, plain, (![D_440]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_440), u1_struct_0(D_440), u1_struct_0('#skF_2')) | ~l1_struct_0(D_440) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3443])).
% 9.30/3.10  tff(c_3448, plain, (![D_440]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_440), u1_struct_0(D_440), u1_struct_0('#skF_2')) | ~l1_struct_0(D_440) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3445])).
% 9.30/3.10  tff(c_3460, plain, (![D_440]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_440), u1_struct_0(D_440), u1_struct_0('#skF_2')) | ~l1_struct_0(D_440) | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3458, c_3448])).
% 9.30/3.10  tff(c_3461, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3460])).
% 9.30/3.10  tff(c_3464, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_3461])).
% 9.30/3.10  tff(c_3468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_3464])).
% 9.30/3.10  tff(c_3470, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3460])).
% 9.30/3.10  tff(c_3475, plain, (![A_443, B_444, C_445, D_446]: (m1_subset_1(k2_tmap_1(A_443, B_444, C_445, D_446), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_446), u1_struct_0(B_444)))) | ~l1_struct_0(D_446) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_443), u1_struct_0(B_444)))) | ~v1_funct_2(C_445, u1_struct_0(A_443), u1_struct_0(B_444)) | ~v1_funct_1(C_445) | ~l1_struct_0(B_444) | ~l1_struct_0(A_443))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_3252, plain, (![A_396, B_397, C_398, D_399]: (v1_funct_1(k2_tmap_1(A_396, B_397, C_398, D_399)) | ~l1_struct_0(D_399) | ~m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_396), u1_struct_0(B_397)))) | ~v1_funct_2(C_398, u1_struct_0(A_396), u1_struct_0(B_397)) | ~v1_funct_1(C_398) | ~l1_struct_0(B_397) | ~l1_struct_0(A_396))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_3256, plain, (![D_399]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_399)) | ~l1_struct_0(D_399) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3252])).
% 9.30/3.10  tff(c_3262, plain, (![D_399]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_399)) | ~l1_struct_0(D_399) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3256])).
% 9.30/3.10  tff(c_3274, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3262])).
% 9.30/3.10  tff(c_3277, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_3274])).
% 9.30/3.10  tff(c_3281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_3277])).
% 9.30/3.10  tff(c_3283, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3262])).
% 9.30/3.10  tff(c_3263, plain, (![A_400, B_401, C_402, D_403]: (v1_funct_2(k2_tmap_1(A_400, B_401, C_402, D_403), u1_struct_0(D_403), u1_struct_0(B_401)) | ~l1_struct_0(D_403) | ~m1_subset_1(C_402, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_400), u1_struct_0(B_401)))) | ~v1_funct_2(C_402, u1_struct_0(A_400), u1_struct_0(B_401)) | ~v1_funct_1(C_402) | ~l1_struct_0(B_401) | ~l1_struct_0(A_400))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_3267, plain, (![D_403]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_403), u1_struct_0(D_403), u1_struct_0('#skF_2')) | ~l1_struct_0(D_403) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3263])).
% 9.30/3.10  tff(c_3273, plain, (![D_403]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_403), u1_struct_0(D_403), u1_struct_0('#skF_2')) | ~l1_struct_0(D_403) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3267])).
% 9.30/3.10  tff(c_3285, plain, (![D_403]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_403), u1_struct_0(D_403), u1_struct_0('#skF_2')) | ~l1_struct_0(D_403) | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3283, c_3273])).
% 9.30/3.10  tff(c_3286, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3285])).
% 9.30/3.10  tff(c_3289, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_3286])).
% 9.30/3.10  tff(c_3293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_3289])).
% 9.30/3.10  tff(c_3295, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3285])).
% 9.30/3.10  tff(c_3344, plain, (![A_412, B_413, C_414, D_415]: (m1_subset_1(k2_tmap_1(A_412, B_413, C_414, D_415), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_415), u1_struct_0(B_413)))) | ~l1_struct_0(D_415) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_412), u1_struct_0(B_413)))) | ~v1_funct_2(C_414, u1_struct_0(A_412), u1_struct_0(B_413)) | ~v1_funct_1(C_414) | ~l1_struct_0(B_413) | ~l1_struct_0(A_412))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_172, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_246, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_172])).
% 9.30/3.10  tff(c_162, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_267, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_162])).
% 9.30/3.10  tff(c_152, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_264, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_152])).
% 9.30/3.10  tff(c_142, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_268, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_142])).
% 9.30/3.10  tff(c_132, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_247, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_132])).
% 9.30/3.10  tff(c_122, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_266, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_122])).
% 9.30/3.10  tff(c_112, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_265, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_112])).
% 9.30/3.10  tff(c_102, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_281, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_102])).
% 9.30/3.10  tff(c_88, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_186, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_88])).
% 9.30/3.10  tff(c_196, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_186])).
% 9.30/3.10  tff(c_206, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_196])).
% 9.30/3.10  tff(c_365, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_267, c_264, c_268, c_247, c_266, c_265, c_281, c_206])).
% 9.30/3.10  tff(c_58, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_60, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_373, plain, (![A_131, B_132, C_133]: (m1_pre_topc(k1_tsep_1(A_131, B_132, C_133), A_131) | ~m1_pre_topc(C_133, A_131) | v2_struct_0(C_133) | ~m1_pre_topc(B_132, A_131) | v2_struct_0(B_132) | ~l1_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.30/3.10  tff(c_379, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_60, c_373])).
% 9.30/3.10  tff(c_382, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_66, c_62, c_379])).
% 9.30/3.10  tff(c_383, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_86, c_68, c_64, c_382])).
% 9.30/3.10  tff(c_84, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_78, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 9.30/3.10  tff(c_314, plain, (![A_118, B_119, C_120, D_121]: (k2_partfun1(A_118, B_119, C_120, D_121)=k7_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_1(C_120))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.30/3.10  tff(c_320, plain, (![D_121]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_121)=k7_relat_1('#skF_3', D_121) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_70, c_314])).
% 9.30/3.10  tff(c_329, plain, (![D_121]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_121)=k7_relat_1('#skF_3', D_121))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_320])).
% 9.30/3.10  tff(c_594, plain, (![A_170, B_171, C_172, D_173]: (k2_partfun1(u1_struct_0(A_170), u1_struct_0(B_171), C_172, u1_struct_0(D_173))=k2_tmap_1(A_170, B_171, C_172, D_173) | ~m1_pre_topc(D_173, A_170) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_170), u1_struct_0(B_171)))) | ~v1_funct_2(C_172, u1_struct_0(A_170), u1_struct_0(B_171)) | ~v1_funct_1(C_172) | ~l1_pre_topc(B_171) | ~v2_pre_topc(B_171) | v2_struct_0(B_171) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.30/3.10  tff(c_602, plain, (![D_173]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_173))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_173) | ~m1_pre_topc(D_173, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_594])).
% 9.30/3.10  tff(c_614, plain, (![D_173]: (k7_relat_1('#skF_3', u1_struct_0(D_173))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_173) | ~m1_pre_topc(D_173, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_78, c_76, c_74, c_72, c_329, c_602])).
% 9.30/3.10  tff(c_616, plain, (![D_174]: (k7_relat_1('#skF_3', u1_struct_0(D_174))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_174) | ~m1_pre_topc(D_174, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_614])).
% 9.30/3.10  tff(c_8, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.30/3.10  tff(c_229, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_8])).
% 9.30/3.10  tff(c_241, plain, (![C_111, A_112, B_113]: (v4_relat_1(C_111, A_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.30/3.10  tff(c_245, plain, (v4_relat_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_241])).
% 9.30/3.10  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.30/3.10  tff(c_248, plain, (![B_114, A_115]: (k7_relat_1(B_114, A_115)=B_114 | ~r1_tarski(k1_relat_1(B_114), A_115) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.30/3.10  tff(c_253, plain, (![B_116, A_117]: (k7_relat_1(B_116, A_117)=B_116 | ~v4_relat_1(B_116, A_117) | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_4, c_248])).
% 9.30/3.10  tff(c_256, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_245, c_253])).
% 9.30/3.10  tff(c_259, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_256])).
% 9.30/3.10  tff(c_622, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_616, c_259])).
% 9.30/3.10  tff(c_631, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_383, c_622])).
% 9.30/3.10  tff(c_2843, plain, (![D_361, C_360, A_357, E_358, B_359]: (v5_pre_topc(k2_tmap_1(A_357, B_359, E_358, k1_tsep_1(A_357, C_360, D_361)), k1_tsep_1(A_357, C_360, D_361), B_359) | ~m1_subset_1(k2_tmap_1(A_357, B_359, E_358, D_361), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_361), u1_struct_0(B_359)))) | ~v5_pre_topc(k2_tmap_1(A_357, B_359, E_358, D_361), D_361, B_359) | ~v1_funct_2(k2_tmap_1(A_357, B_359, E_358, D_361), u1_struct_0(D_361), u1_struct_0(B_359)) | ~v1_funct_1(k2_tmap_1(A_357, B_359, E_358, D_361)) | ~m1_subset_1(k2_tmap_1(A_357, B_359, E_358, C_360), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360), u1_struct_0(B_359)))) | ~v5_pre_topc(k2_tmap_1(A_357, B_359, E_358, C_360), C_360, B_359) | ~v1_funct_2(k2_tmap_1(A_357, B_359, E_358, C_360), u1_struct_0(C_360), u1_struct_0(B_359)) | ~v1_funct_1(k2_tmap_1(A_357, B_359, E_358, C_360)) | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_357), u1_struct_0(B_359)))) | ~v1_funct_2(E_358, u1_struct_0(A_357), u1_struct_0(B_359)) | ~v1_funct_1(E_358) | ~r4_tsep_1(A_357, C_360, D_361) | ~m1_pre_topc(D_361, A_357) | v2_struct_0(D_361) | ~m1_pre_topc(C_360, A_357) | v2_struct_0(C_360) | ~l1_pre_topc(B_359) | ~v2_pre_topc(B_359) | v2_struct_0(B_359) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357) | v2_struct_0(A_357))), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.30/3.10  tff(c_2855, plain, (![C_360]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_360, '#skF_5')), k1_tsep_1('#skF_1', C_360, '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), C_360, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), u1_struct_0(C_360), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~r4_tsep_1('#skF_1', C_360, '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_360, '#skF_1') | v2_struct_0(C_360) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_281, c_2843])).
% 9.30/3.10  tff(c_2873, plain, (![C_360]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_360, '#skF_5')), k1_tsep_1('#skF_1', C_360, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), C_360, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), u1_struct_0(C_360), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360)) | ~r4_tsep_1('#skF_1', C_360, '#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_360, '#skF_1') | v2_struct_0(C_360) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_78, c_76, c_62, c_74, c_72, c_70, c_247, c_266, c_265, c_2855])).
% 9.30/3.10  tff(c_3144, plain, (![C_377]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_377, '#skF_5')), k1_tsep_1('#skF_1', C_377, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_377), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_377), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_377), C_377, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_377), u1_struct_0(C_377), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_377)) | ~r4_tsep_1('#skF_1', C_377, '#skF_5') | ~m1_pre_topc(C_377, '#skF_1') | v2_struct_0(C_377))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_64, c_2873])).
% 9.30/3.10  tff(c_3157, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_268, c_3144])).
% 9.30/3.10  tff(c_3170, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_58, c_246, c_267, c_264, c_631, c_60, c_60, c_3157])).
% 9.30/3.10  tff(c_3172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_365, c_3170])).
% 9.30/3.10  tff(c_3174, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_102])).
% 9.30/3.10  tff(c_3353, plain, (~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3344, c_3174])).
% 9.30/3.10  tff(c_3368, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3283, c_3295, c_74, c_72, c_70, c_3353])).
% 9.30/3.10  tff(c_3374, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_16, c_3368])).
% 9.30/3.10  tff(c_3378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_224, c_3374])).
% 9.30/3.10  tff(c_3380, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_142])).
% 9.30/3.10  tff(c_3484, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3475, c_3380])).
% 9.30/3.10  tff(c_3499, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3458, c_3470, c_74, c_72, c_70, c_3484])).
% 9.30/3.10  tff(c_3515, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_3499])).
% 9.30/3.10  tff(c_3519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_3515])).
% 9.30/3.10  tff(c_3521, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_162])).
% 9.30/3.10  tff(c_3617, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_3613, c_3521])).
% 9.30/3.10  tff(c_3620, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_3617])).
% 9.30/3.10  tff(c_3624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_3620])).
% 9.30/3.10  tff(c_3626, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_122])).
% 9.30/3.10  tff(c_3722, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_3718, c_3626])).
% 9.30/3.10  tff(c_3747, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_16, c_3722])).
% 9.30/3.10  tff(c_3751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_224, c_3747])).
% 9.30/3.10  tff(c_3753, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_112])).
% 9.30/3.10  tff(c_3811, plain, (![A_525, B_526, C_527, D_528]: (v1_funct_1(k2_tmap_1(A_525, B_526, C_527, D_528)) | ~l1_struct_0(D_528) | ~m1_subset_1(C_527, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_525), u1_struct_0(B_526)))) | ~v1_funct_2(C_527, u1_struct_0(A_525), u1_struct_0(B_526)) | ~v1_funct_1(C_527) | ~l1_struct_0(B_526) | ~l1_struct_0(A_525))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.10  tff(c_3813, plain, (![D_528]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_528)) | ~l1_struct_0(D_528) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3811])).
% 9.30/3.10  tff(c_3816, plain, (![D_528]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_528)) | ~l1_struct_0(D_528) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3813])).
% 9.30/3.10  tff(c_3817, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3816])).
% 9.30/3.10  tff(c_3820, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_3817])).
% 9.30/3.10  tff(c_3824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_3820])).
% 9.30/3.10  tff(c_3826, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3816])).
% 9.30/3.10  tff(c_3787, plain, (![A_519, B_520, C_521]: (m1_pre_topc(k1_tsep_1(A_519, B_520, C_521), A_519) | ~m1_pre_topc(C_521, A_519) | v2_struct_0(C_521) | ~m1_pre_topc(B_520, A_519) | v2_struct_0(B_520) | ~l1_pre_topc(A_519) | v2_struct_0(A_519))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.30/3.10  tff(c_3793, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_60, c_3787])).
% 9.30/3.10  tff(c_3796, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_66, c_62, c_3793])).
% 9.30/3.10  tff(c_3797, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_86, c_68, c_64, c_3796])).
% 9.30/3.10  tff(c_3758, plain, (![A_508, B_509, C_510, D_511]: (k2_partfun1(A_508, B_509, C_510, D_511)=k7_relat_1(C_510, D_511) | ~m1_subset_1(C_510, k1_zfmisc_1(k2_zfmisc_1(A_508, B_509))) | ~v1_funct_1(C_510))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.30/3.10  tff(c_3760, plain, (![D_511]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_511)=k7_relat_1('#skF_3', D_511) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_70, c_3758])).
% 9.30/3.10  tff(c_3763, plain, (![D_511]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_511)=k7_relat_1('#skF_3', D_511))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3760])).
% 9.30/3.10  tff(c_3888, plain, (![A_548, B_549, C_550, D_551]: (k2_partfun1(u1_struct_0(A_548), u1_struct_0(B_549), C_550, u1_struct_0(D_551))=k2_tmap_1(A_548, B_549, C_550, D_551) | ~m1_pre_topc(D_551, A_548) | ~m1_subset_1(C_550, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_548), u1_struct_0(B_549)))) | ~v1_funct_2(C_550, u1_struct_0(A_548), u1_struct_0(B_549)) | ~v1_funct_1(C_550) | ~l1_pre_topc(B_549) | ~v2_pre_topc(B_549) | v2_struct_0(B_549) | ~l1_pre_topc(A_548) | ~v2_pre_topc(A_548) | v2_struct_0(A_548))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.30/3.10  tff(c_3892, plain, (![D_551]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_551))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_551) | ~m1_pre_topc(D_551, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3888])).
% 9.30/3.11  tff(c_3896, plain, (![D_551]: (k7_relat_1('#skF_3', u1_struct_0(D_551))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_551) | ~m1_pre_topc(D_551, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_78, c_76, c_74, c_72, c_3763, c_3892])).
% 9.30/3.11  tff(c_3903, plain, (![D_553]: (k7_relat_1('#skF_3', u1_struct_0(D_553))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_553) | ~m1_pre_topc(D_553, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_3896])).
% 9.30/3.11  tff(c_3909, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3903, c_259])).
% 9.30/3.11  tff(c_3918, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3797, c_3909])).
% 9.30/3.11  tff(c_3752, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_112])).
% 9.30/3.11  tff(c_3825, plain, (![D_528]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_528)) | ~l1_struct_0(D_528))), inference(splitRight, [status(thm)], [c_3816])).
% 9.30/3.11  tff(c_3833, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3825])).
% 9.30/3.11  tff(c_3836, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_3833])).
% 9.30/3.11  tff(c_3840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_3836])).
% 9.30/3.11  tff(c_3841, plain, (![D_528]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_528)) | ~l1_struct_0(D_528))), inference(splitRight, [status(thm)], [c_3825])).
% 9.30/3.11  tff(c_3842, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3825])).
% 9.30/3.11  tff(c_3847, plain, (![A_535, B_536, C_537, D_538]: (m1_subset_1(k2_tmap_1(A_535, B_536, C_537, D_538), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_538), u1_struct_0(B_536)))) | ~l1_struct_0(D_538) | ~m1_subset_1(C_537, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_535), u1_struct_0(B_536)))) | ~v1_funct_2(C_537, u1_struct_0(A_535), u1_struct_0(B_536)) | ~v1_funct_1(C_537) | ~l1_struct_0(B_536) | ~l1_struct_0(A_535))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.11  tff(c_3869, plain, (![A_539, B_540, C_541, D_542]: (v1_relat_1(k2_tmap_1(A_539, B_540, C_541, D_542)) | ~l1_struct_0(D_542) | ~m1_subset_1(C_541, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_539), u1_struct_0(B_540)))) | ~v1_funct_2(C_541, u1_struct_0(A_539), u1_struct_0(B_540)) | ~v1_funct_1(C_541) | ~l1_struct_0(B_540) | ~l1_struct_0(A_539))), inference(resolution, [status(thm)], [c_3847, c_8])).
% 9.30/3.11  tff(c_3873, plain, (![D_542]: (v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_542)) | ~l1_struct_0(D_542) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3869])).
% 9.30/3.11  tff(c_3877, plain, (![D_542]: (v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_542)) | ~l1_struct_0(D_542))), inference(demodulation, [status(thm), theory('equality')], [c_3826, c_3842, c_74, c_72, c_3873])).
% 9.30/3.11  tff(c_3827, plain, (![A_529, B_530, C_531, D_532]: (v1_funct_2(k2_tmap_1(A_529, B_530, C_531, D_532), u1_struct_0(D_532), u1_struct_0(B_530)) | ~l1_struct_0(D_532) | ~m1_subset_1(C_531, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_529), u1_struct_0(B_530)))) | ~v1_funct_2(C_531, u1_struct_0(A_529), u1_struct_0(B_530)) | ~v1_funct_1(C_531) | ~l1_struct_0(B_530) | ~l1_struct_0(A_529))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.11  tff(c_3829, plain, (![D_532]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_532), u1_struct_0(D_532), u1_struct_0('#skF_2')) | ~l1_struct_0(D_532) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3827])).
% 9.30/3.11  tff(c_3832, plain, (![D_532]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_532), u1_struct_0(D_532), u1_struct_0('#skF_2')) | ~l1_struct_0(D_532) | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3826, c_74, c_72, c_3829])).
% 9.30/3.11  tff(c_3844, plain, (![D_532]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_532), u1_struct_0(D_532), u1_struct_0('#skF_2')) | ~l1_struct_0(D_532))), inference(demodulation, [status(thm), theory('equality')], [c_3842, c_3832])).
% 9.30/3.11  tff(c_28, plain, (![A_37, B_38, C_39, D_40]: (m1_subset_1(k2_tmap_1(A_37, B_38, C_39, D_40), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_40), u1_struct_0(B_38)))) | ~l1_struct_0(D_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_37), u1_struct_0(B_38)))) | ~v1_funct_2(C_39, u1_struct_0(A_37), u1_struct_0(B_38)) | ~v1_funct_1(C_39) | ~l1_struct_0(B_38) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.30/3.11  tff(c_4157, plain, (![C_615, A_611, B_612, D_614, D_613]: (k2_partfun1(u1_struct_0(D_613), u1_struct_0(B_612), k2_tmap_1(A_611, B_612, C_615, D_613), u1_struct_0(D_614))=k2_tmap_1(D_613, B_612, k2_tmap_1(A_611, B_612, C_615, D_613), D_614) | ~m1_pre_topc(D_614, D_613) | ~v1_funct_2(k2_tmap_1(A_611, B_612, C_615, D_613), u1_struct_0(D_613), u1_struct_0(B_612)) | ~v1_funct_1(k2_tmap_1(A_611, B_612, C_615, D_613)) | ~l1_pre_topc(B_612) | ~v2_pre_topc(B_612) | v2_struct_0(B_612) | ~l1_pre_topc(D_613) | ~v2_pre_topc(D_613) | v2_struct_0(D_613) | ~l1_struct_0(D_613) | ~m1_subset_1(C_615, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_611), u1_struct_0(B_612)))) | ~v1_funct_2(C_615, u1_struct_0(A_611), u1_struct_0(B_612)) | ~v1_funct_1(C_615) | ~l1_struct_0(B_612) | ~l1_struct_0(A_611))), inference(resolution, [status(thm)], [c_28, c_3888])).
% 9.30/3.11  tff(c_4161, plain, (![D_613, D_614]: (k2_partfun1(u1_struct_0(D_613), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_613), u1_struct_0(D_614))=k2_tmap_1(D_613, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_613), D_614) | ~m1_pre_topc(D_614, D_613) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_613), u1_struct_0(D_613), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_613)) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(D_613) | ~v2_pre_topc(D_613) | v2_struct_0(D_613) | ~l1_struct_0(D_613) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_4157])).
% 9.30/3.11  tff(c_4165, plain, (![D_613, D_614]: (k2_partfun1(u1_struct_0(D_613), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_613), u1_struct_0(D_614))=k2_tmap_1(D_613, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_613), D_614) | ~m1_pre_topc(D_614, D_613) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_613), u1_struct_0(D_613), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_613)) | v2_struct_0('#skF_2') | ~l1_pre_topc(D_613) | ~v2_pre_topc(D_613) | v2_struct_0(D_613) | ~l1_struct_0(D_613))), inference(demodulation, [status(thm), theory('equality')], [c_3826, c_3842, c_74, c_72, c_78, c_76, c_4161])).
% 9.30/3.11  tff(c_4167, plain, (![D_616, D_617]: (k2_partfun1(u1_struct_0(D_616), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_616), u1_struct_0(D_617))=k2_tmap_1(D_616, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_616), D_617) | ~m1_pre_topc(D_617, D_616) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_616), u1_struct_0(D_616), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_616)) | ~l1_pre_topc(D_616) | ~v2_pre_topc(D_616) | v2_struct_0(D_616) | ~l1_struct_0(D_616))), inference(negUnitSimplification, [status(thm)], [c_80, c_4165])).
% 9.30/3.11  tff(c_14, plain, (![A_11, B_12, C_13, D_14]: (k2_partfun1(A_11, B_12, C_13, D_14)=k7_relat_1(C_13, D_14) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.30/3.11  tff(c_3981, plain, (![A_562, D_561, D_563, C_564, B_560]: (k2_partfun1(u1_struct_0(D_561), u1_struct_0(B_560), k2_tmap_1(A_562, B_560, C_564, D_561), D_563)=k7_relat_1(k2_tmap_1(A_562, B_560, C_564, D_561), D_563) | ~v1_funct_1(k2_tmap_1(A_562, B_560, C_564, D_561)) | ~l1_struct_0(D_561) | ~m1_subset_1(C_564, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_562), u1_struct_0(B_560)))) | ~v1_funct_2(C_564, u1_struct_0(A_562), u1_struct_0(B_560)) | ~v1_funct_1(C_564) | ~l1_struct_0(B_560) | ~l1_struct_0(A_562))), inference(resolution, [status(thm)], [c_3847, c_14])).
% 9.30/3.11  tff(c_3985, plain, (![D_561, D_563]: (k2_partfun1(u1_struct_0(D_561), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_561), D_563)=k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_561), D_563) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_561)) | ~l1_struct_0(D_561) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3981])).
% 9.30/3.11  tff(c_3989, plain, (![D_561, D_563]: (k2_partfun1(u1_struct_0(D_561), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_561), D_563)=k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_561), D_563) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_561)) | ~l1_struct_0(D_561))), inference(demodulation, [status(thm), theory('equality')], [c_3826, c_3842, c_74, c_72, c_3985])).
% 9.30/3.11  tff(c_4189, plain, (![D_618, D_619]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_618), u1_struct_0(D_619))=k2_tmap_1(D_618, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_618), D_619) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_618)) | ~l1_struct_0(D_618) | ~m1_pre_topc(D_619, D_618) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_618), u1_struct_0(D_618), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_618)) | ~l1_pre_topc(D_618) | ~v2_pre_topc(D_618) | v2_struct_0(D_618) | ~l1_struct_0(D_618))), inference(superposition, [status(thm), theory('equality')], [c_4167, c_3989])).
% 9.30/3.11  tff(c_4198, plain, (![D_620, D_621]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_620), u1_struct_0(D_621))=k2_tmap_1(D_620, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_620), D_621) | ~m1_pre_topc(D_621, D_620) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_620)) | ~l1_pre_topc(D_620) | ~v2_pre_topc(D_620) | v2_struct_0(D_620) | ~l1_struct_0(D_620))), inference(resolution, [status(thm)], [c_3844, c_4189])).
% 9.30/3.11  tff(c_12, plain, (![C_10, A_8, B_9]: (v4_relat_1(C_10, A_8) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.30/3.11  tff(c_3879, plain, (![A_544, B_545, C_546, D_547]: (v4_relat_1(k2_tmap_1(A_544, B_545, C_546, D_547), u1_struct_0(D_547)) | ~l1_struct_0(D_547) | ~m1_subset_1(C_546, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_544), u1_struct_0(B_545)))) | ~v1_funct_2(C_546, u1_struct_0(A_544), u1_struct_0(B_545)) | ~v1_funct_1(C_546) | ~l1_struct_0(B_545) | ~l1_struct_0(A_544))), inference(resolution, [status(thm)], [c_3847, c_12])).
% 9.30/3.11  tff(c_3883, plain, (![D_547]: (v4_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_547), u1_struct_0(D_547)) | ~l1_struct_0(D_547) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3879])).
% 9.30/3.11  tff(c_3898, plain, (![D_552]: (v4_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_552), u1_struct_0(D_552)) | ~l1_struct_0(D_552))), inference(demodulation, [status(thm), theory('equality')], [c_3826, c_3842, c_74, c_72, c_3883])).
% 9.30/3.11  tff(c_252, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_248])).
% 9.30/3.11  tff(c_3902, plain, (![D_552]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_552), u1_struct_0(D_552))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_552) | ~v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_552)) | ~l1_struct_0(D_552))), inference(resolution, [status(thm)], [c_3898, c_252])).
% 9.30/3.11  tff(c_4696, plain, (![D_662]: (k2_tmap_1(D_662, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_662), D_662)=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_662) | ~v1_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_662)) | ~l1_struct_0(D_662) | ~m1_pre_topc(D_662, D_662) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_662)) | ~l1_pre_topc(D_662) | ~v2_pre_topc(D_662) | v2_struct_0(D_662) | ~l1_struct_0(D_662))), inference(superposition, [status(thm), theory('equality')], [c_4198, c_3902])).
% 9.30/3.11  tff(c_4705, plain, (![D_663]: (k2_tmap_1(D_663, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_663), D_663)=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_663) | ~m1_pre_topc(D_663, D_663) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_663)) | ~l1_pre_topc(D_663) | ~v2_pre_topc(D_663) | v2_struct_0(D_663) | ~l1_struct_0(D_663))), inference(resolution, [status(thm)], [c_3877, c_4696])).
% 9.30/3.11  tff(c_4717, plain, (![D_528]: (k2_tmap_1(D_528, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_528), D_528)=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_528) | ~m1_pre_topc(D_528, D_528) | ~l1_pre_topc(D_528) | ~v2_pre_topc(D_528) | v2_struct_0(D_528) | ~l1_struct_0(D_528))), inference(resolution, [status(thm)], [c_3841, c_4705])).
% 9.30/3.11  tff(c_4662, plain, (![A_656, D_660, C_659, E_657, B_658]: (v5_pre_topc(k2_tmap_1(A_656, B_658, E_657, D_660), D_660, B_658) | ~m1_subset_1(k2_tmap_1(A_656, B_658, E_657, k1_tsep_1(A_656, C_659, D_660)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_656, C_659, D_660)), u1_struct_0(B_658)))) | ~v5_pre_topc(k2_tmap_1(A_656, B_658, E_657, k1_tsep_1(A_656, C_659, D_660)), k1_tsep_1(A_656, C_659, D_660), B_658) | ~v1_funct_2(k2_tmap_1(A_656, B_658, E_657, k1_tsep_1(A_656, C_659, D_660)), u1_struct_0(k1_tsep_1(A_656, C_659, D_660)), u1_struct_0(B_658)) | ~v1_funct_1(k2_tmap_1(A_656, B_658, E_657, k1_tsep_1(A_656, C_659, D_660))) | ~m1_subset_1(E_657, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_656), u1_struct_0(B_658)))) | ~v1_funct_2(E_657, u1_struct_0(A_656), u1_struct_0(B_658)) | ~v1_funct_1(E_657) | ~r4_tsep_1(A_656, C_659, D_660) | ~m1_pre_topc(D_660, A_656) | v2_struct_0(D_660) | ~m1_pre_topc(C_659, A_656) | v2_struct_0(C_659) | ~l1_pre_topc(B_658) | ~v2_pre_topc(B_658) | v2_struct_0(B_658) | ~l1_pre_topc(A_656) | ~v2_pre_topc(A_656) | v2_struct_0(A_656))), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.30/3.11  tff(c_4673, plain, (![B_658, E_657]: (v5_pre_topc(k2_tmap_1('#skF_1', B_658, E_657, '#skF_5'), '#skF_5', B_658) | ~m1_subset_1(k2_tmap_1('#skF_1', B_658, E_657, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_658)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_658, E_657, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_658) | ~v1_funct_2(k2_tmap_1('#skF_1', B_658, E_657, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_658)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_658, E_657, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_657, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_658)))) | ~v1_funct_2(E_657, u1_struct_0('#skF_1'), u1_struct_0(B_658)) | ~v1_funct_1(E_657) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_658) | ~v2_pre_topc(B_658) | v2_struct_0(B_658) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_4662])).
% 9.30/3.11  tff(c_4682, plain, (![B_658, E_657]: (v5_pre_topc(k2_tmap_1('#skF_1', B_658, E_657, '#skF_5'), '#skF_5', B_658) | ~m1_subset_1(k2_tmap_1('#skF_1', B_658, E_657, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_658)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_658, E_657, '#skF_1'), '#skF_1', B_658) | ~v1_funct_2(k2_tmap_1('#skF_1', B_658, E_657, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_658)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_658, E_657, '#skF_1')) | ~m1_subset_1(E_657, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_658)))) | ~v1_funct_2(E_657, u1_struct_0('#skF_1'), u1_struct_0(B_658)) | ~v1_funct_1(E_657) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_658) | ~v2_pre_topc(B_658) | v2_struct_0(B_658) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_66, c_62, c_58, c_60, c_60, c_60, c_60, c_60, c_60, c_4673])).
% 9.30/3.11  tff(c_5257, plain, (![B_693, E_694]: (v5_pre_topc(k2_tmap_1('#skF_1', B_693, E_694, '#skF_5'), '#skF_5', B_693) | ~m1_subset_1(k2_tmap_1('#skF_1', B_693, E_694, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_693)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_693, E_694, '#skF_1'), '#skF_1', B_693) | ~v1_funct_2(k2_tmap_1('#skF_1', B_693, E_694, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_693)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_693, E_694, '#skF_1')) | ~m1_subset_1(E_694, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_693)))) | ~v1_funct_2(E_694, u1_struct_0('#skF_1'), u1_struct_0(B_693)) | ~v1_funct_1(E_694) | ~l1_pre_topc(B_693) | ~v2_pre_topc(B_693) | v2_struct_0(B_693))), inference(negUnitSimplification, [status(thm)], [c_86, c_68, c_64, c_4682])).
% 9.30/3.11  tff(c_5261, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_5'), '#skF_5', '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4717, c_5257])).
% 9.30/3.11  tff(c_5274, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3826, c_84, c_82, c_3797, c_78, c_76, c_74, c_3918, c_72, c_3918, c_70, c_3918, c_74, c_3918, c_3918, c_72, c_3918, c_3918, c_3752, c_3918, c_3918, c_70, c_3918, c_3918, c_5261])).
% 9.30/3.11  tff(c_5276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_3753, c_5274])).
% 9.30/3.11  tff(c_5278, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_152])).
% 9.30/3.11  tff(c_5315, plain, (![A_706, B_707, C_708]: (m1_pre_topc(k1_tsep_1(A_706, B_707, C_708), A_706) | ~m1_pre_topc(C_708, A_706) | v2_struct_0(C_708) | ~m1_pre_topc(B_707, A_706) | v2_struct_0(B_707) | ~l1_pre_topc(A_706) | v2_struct_0(A_706))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.30/3.11  tff(c_5321, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_60, c_5315])).
% 9.30/3.11  tff(c_5324, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_66, c_62, c_5321])).
% 9.30/3.11  tff(c_5325, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_86, c_68, c_64, c_5324])).
% 9.30/3.11  tff(c_5283, plain, (![A_695, B_696, C_697, D_698]: (k2_partfun1(A_695, B_696, C_697, D_698)=k7_relat_1(C_697, D_698) | ~m1_subset_1(C_697, k1_zfmisc_1(k2_zfmisc_1(A_695, B_696))) | ~v1_funct_1(C_697))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.30/3.11  tff(c_5285, plain, (![D_698]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_698)=k7_relat_1('#skF_3', D_698) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_70, c_5283])).
% 9.30/3.11  tff(c_5288, plain, (![D_698]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_698)=k7_relat_1('#skF_3', D_698))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5285])).
% 9.30/3.11  tff(c_5405, plain, (![A_731, B_732, C_733, D_734]: (k2_partfun1(u1_struct_0(A_731), u1_struct_0(B_732), C_733, u1_struct_0(D_734))=k2_tmap_1(A_731, B_732, C_733, D_734) | ~m1_pre_topc(D_734, A_731) | ~m1_subset_1(C_733, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_731), u1_struct_0(B_732)))) | ~v1_funct_2(C_733, u1_struct_0(A_731), u1_struct_0(B_732)) | ~v1_funct_1(C_733) | ~l1_pre_topc(B_732) | ~v2_pre_topc(B_732) | v2_struct_0(B_732) | ~l1_pre_topc(A_731) | ~v2_pre_topc(A_731) | v2_struct_0(A_731))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.30/3.11  tff(c_5409, plain, (![D_734]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_734))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_734) | ~m1_pre_topc(D_734, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_5405])).
% 9.30/3.11  tff(c_5413, plain, (![D_734]: (k7_relat_1('#skF_3', u1_struct_0(D_734))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_734) | ~m1_pre_topc(D_734, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_78, c_76, c_74, c_72, c_5288, c_5409])).
% 9.30/3.11  tff(c_5415, plain, (![D_735]: (k7_relat_1('#skF_3', u1_struct_0(D_735))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_735) | ~m1_pre_topc(D_735, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_5413])).
% 9.30/3.11  tff(c_5421, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5415, c_259])).
% 9.30/3.11  tff(c_5430, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5325, c_5421])).
% 9.30/3.11  tff(c_5277, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_152])).
% 9.30/3.11  tff(c_5815, plain, (![E_824, D_827, A_823, C_826, B_825]: (v5_pre_topc(k2_tmap_1(A_823, B_825, E_824, C_826), C_826, B_825) | ~m1_subset_1(k2_tmap_1(A_823, B_825, E_824, k1_tsep_1(A_823, C_826, D_827)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_823, C_826, D_827)), u1_struct_0(B_825)))) | ~v5_pre_topc(k2_tmap_1(A_823, B_825, E_824, k1_tsep_1(A_823, C_826, D_827)), k1_tsep_1(A_823, C_826, D_827), B_825) | ~v1_funct_2(k2_tmap_1(A_823, B_825, E_824, k1_tsep_1(A_823, C_826, D_827)), u1_struct_0(k1_tsep_1(A_823, C_826, D_827)), u1_struct_0(B_825)) | ~v1_funct_1(k2_tmap_1(A_823, B_825, E_824, k1_tsep_1(A_823, C_826, D_827))) | ~m1_subset_1(E_824, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_823), u1_struct_0(B_825)))) | ~v1_funct_2(E_824, u1_struct_0(A_823), u1_struct_0(B_825)) | ~v1_funct_1(E_824) | ~r4_tsep_1(A_823, C_826, D_827) | ~m1_pre_topc(D_827, A_823) | v2_struct_0(D_827) | ~m1_pre_topc(C_826, A_823) | v2_struct_0(C_826) | ~l1_pre_topc(B_825) | ~v2_pre_topc(B_825) | v2_struct_0(B_825) | ~l1_pre_topc(A_823) | ~v2_pre_topc(A_823) | v2_struct_0(A_823))), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.30/3.11  tff(c_5822, plain, (![B_825, E_824]: (v5_pre_topc(k2_tmap_1('#skF_1', B_825, E_824, '#skF_4'), '#skF_4', B_825) | ~m1_subset_1(k2_tmap_1('#skF_1', B_825, E_824, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_825)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_825, E_824, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_825) | ~v1_funct_2(k2_tmap_1('#skF_1', B_825, E_824, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_825)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_825, E_824, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_824, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_825)))) | ~v1_funct_2(E_824, u1_struct_0('#skF_1'), u1_struct_0(B_825)) | ~v1_funct_1(E_824) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_825) | ~v2_pre_topc(B_825) | v2_struct_0(B_825) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_5815])).
% 9.30/3.11  tff(c_5828, plain, (![B_825, E_824]: (v5_pre_topc(k2_tmap_1('#skF_1', B_825, E_824, '#skF_4'), '#skF_4', B_825) | ~m1_subset_1(k2_tmap_1('#skF_1', B_825, E_824, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_825)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_825, E_824, '#skF_1'), '#skF_1', B_825) | ~v1_funct_2(k2_tmap_1('#skF_1', B_825, E_824, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_825)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_825, E_824, '#skF_1')) | ~m1_subset_1(E_824, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_825)))) | ~v1_funct_2(E_824, u1_struct_0('#skF_1'), u1_struct_0(B_825)) | ~v1_funct_1(E_824) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_825) | ~v2_pre_topc(B_825) | v2_struct_0(B_825) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_66, c_62, c_58, c_60, c_60, c_60, c_60, c_60, c_60, c_5822])).
% 9.30/3.11  tff(c_6094, plain, (![B_851, E_852]: (v5_pre_topc(k2_tmap_1('#skF_1', B_851, E_852, '#skF_4'), '#skF_4', B_851) | ~m1_subset_1(k2_tmap_1('#skF_1', B_851, E_852, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_851)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_851, E_852, '#skF_1'), '#skF_1', B_851) | ~v1_funct_2(k2_tmap_1('#skF_1', B_851, E_852, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_851)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_851, E_852, '#skF_1')) | ~m1_subset_1(E_852, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_851)))) | ~v1_funct_2(E_852, u1_struct_0('#skF_1'), u1_struct_0(B_851)) | ~v1_funct_1(E_852) | ~l1_pre_topc(B_851) | ~v2_pre_topc(B_851) | v2_struct_0(B_851))), inference(negUnitSimplification, [status(thm)], [c_86, c_68, c_64, c_5828])).
% 9.30/3.11  tff(c_6097, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5430, c_6094])).
% 9.30/3.11  tff(c_6103, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_74, c_5430, c_72, c_5430, c_5277, c_5430, c_70, c_6097])).
% 9.30/3.11  tff(c_6105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_5278, c_6103])).
% 9.30/3.11  tff(c_6107, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_132])).
% 9.30/3.11  tff(c_6221, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_6217, c_6107])).
% 9.30/3.11  tff(c_6224, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_16, c_6221])).
% 9.30/3.11  tff(c_6228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_224, c_6224])).
% 9.30/3.11  tff(c_6230, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_172])).
% 9.30/3.11  tff(c_6348, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_6344, c_6230])).
% 9.30/3.11  tff(c_6351, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_6348])).
% 9.30/3.11  tff(c_6355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_6351])).
% 9.30/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.30/3.11  
% 9.30/3.11  Inference rules
% 9.30/3.11  ----------------------
% 9.30/3.11  #Ref     : 0
% 9.30/3.11  #Sup     : 1179
% 9.30/3.11  #Fact    : 0
% 9.30/3.11  #Define  : 0
% 9.30/3.11  #Split   : 39
% 9.30/3.11  #Chain   : 0
% 9.30/3.11  #Close   : 0
% 9.30/3.11  
% 9.30/3.11  Ordering : KBO
% 9.30/3.11  
% 9.30/3.11  Simplification rules
% 9.30/3.11  ----------------------
% 9.30/3.11  #Subsume      : 368
% 9.30/3.11  #Demod        : 3897
% 9.30/3.11  #Tautology    : 358
% 9.30/3.11  #SimpNegUnit  : 348
% 9.30/3.11  #BackRed      : 0
% 9.30/3.11  
% 9.30/3.11  #Partial instantiations: 0
% 9.30/3.11  #Strategies tried      : 1
% 9.30/3.11  
% 9.30/3.11  Timing (in seconds)
% 9.30/3.11  ----------------------
% 9.30/3.11  Preprocessing        : 0.48
% 9.30/3.11  Parsing              : 0.24
% 9.30/3.11  CNF conversion       : 0.06
% 9.30/3.11  Main loop            : 1.75
% 9.30/3.11  Inferencing          : 0.61
% 9.30/3.11  Reduction            : 0.65
% 9.30/3.11  Demodulation         : 0.49
% 9.30/3.11  BG Simplification    : 0.08
% 9.30/3.11  Subsumption          : 0.34
% 9.30/3.11  Abstraction          : 0.08
% 9.30/3.11  MUC search           : 0.00
% 9.30/3.11  Cooper               : 0.00
% 9.30/3.11  Total                : 2.32
% 9.30/3.11  Index Insertion      : 0.00
% 9.30/3.11  Index Deletion       : 0.00
% 9.30/3.11  Index Matching       : 0.00
% 9.30/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
