%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1818+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:28 EST 2020

% Result     : Theorem 5.40s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 718 expanded)
%              Number of leaves         :   31 ( 272 expanded)
%              Depth                    :   13
%              Number of atoms          :  715 (6939 expanded)
%              Number of equality atoms :   20 ( 214 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_216,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
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

tff(f_151,axiom,(
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

tff(f_132,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => k1_tsep_1(A,B,C) = k1_tsep_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_196,plain,(
    ! [B_77,A_78] :
      ( l1_pre_topc(B_77)
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_199,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_196])).

tff(c_205,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_199])).

tff(c_10,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_56,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1845,plain,(
    ! [A_507,B_508,C_509,D_510] :
      ( v1_funct_1(k2_tmap_1(A_507,B_508,C_509,D_510))
      | ~ l1_struct_0(D_510)
      | ~ m1_subset_1(C_509,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_507),u1_struct_0(B_508))))
      | ~ v1_funct_2(C_509,u1_struct_0(A_507),u1_struct_0(B_508))
      | ~ v1_funct_1(C_509)
      | ~ l1_struct_0(B_508)
      | ~ l1_struct_0(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1847,plain,(
    ! [D_510] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_510))
      | ~ l1_struct_0(D_510)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_1845])).

tff(c_1850,plain,(
    ! [D_510] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_510))
      | ~ l1_struct_0(D_510)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1847])).

tff(c_1851,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1850])).

tff(c_1854,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_1851])).

tff(c_1858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1854])).

tff(c_1859,plain,(
    ! [D_510] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_510))
      | ~ l1_struct_0(D_510) ) ),
    inference(splitRight,[status(thm)],[c_1850])).

tff(c_1861,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1859])).

tff(c_1864,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_1861])).

tff(c_1868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1864])).

tff(c_1877,plain,(
    ! [D_515] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_515))
      | ~ l1_struct_0(D_515) ) ),
    inference(splitRight,[status(thm)],[c_1859])).

tff(c_42,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_202,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_196])).

tff(c_208,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_202])).

tff(c_1752,plain,(
    ! [A_494,B_495,C_496,D_497] :
      ( v1_funct_1(k2_tmap_1(A_494,B_495,C_496,D_497))
      | ~ l1_struct_0(D_497)
      | ~ m1_subset_1(C_496,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_494),u1_struct_0(B_495))))
      | ~ v1_funct_2(C_496,u1_struct_0(A_494),u1_struct_0(B_495))
      | ~ v1_funct_1(C_496)
      | ~ l1_struct_0(B_495)
      | ~ l1_struct_0(A_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1754,plain,(
    ! [D_497] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_497))
      | ~ l1_struct_0(D_497)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_1752])).

tff(c_1757,plain,(
    ! [D_497] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_497))
      | ~ l1_struct_0(D_497)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1754])).

tff(c_1758,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1757])).

tff(c_1761,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_1758])).

tff(c_1765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1761])).

tff(c_1766,plain,(
    ! [D_497] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_497))
      | ~ l1_struct_0(D_497) ) ),
    inference(splitRight,[status(thm)],[c_1757])).

tff(c_1768,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1766])).

tff(c_1771,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_1768])).

tff(c_1775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1771])).

tff(c_1778,plain,(
    ! [D_498] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_498))
      | ~ l1_struct_0(D_498) ) ),
    inference(splitRight,[status(thm)],[c_1766])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1122,plain,(
    ! [A_284,B_285,C_286,D_287] :
      ( v1_funct_1(k2_tmap_1(A_284,B_285,C_286,D_287))
      | ~ l1_struct_0(D_287)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_284),u1_struct_0(B_285))))
      | ~ v1_funct_2(C_286,u1_struct_0(A_284),u1_struct_0(B_285))
      | ~ v1_funct_1(C_286)
      | ~ l1_struct_0(B_285)
      | ~ l1_struct_0(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1124,plain,(
    ! [D_287] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_287))
      | ~ l1_struct_0(D_287)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_1122])).

tff(c_1127,plain,(
    ! [D_287] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_287))
      | ~ l1_struct_0(D_287)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1124])).

tff(c_1128,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1127])).

tff(c_1131,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_1128])).

tff(c_1135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1131])).

tff(c_1137,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1127])).

tff(c_1136,plain,(
    ! [D_287] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_287))
      | ~ l1_struct_0(D_287) ) ),
    inference(splitRight,[status(thm)],[c_1127])).

tff(c_1138,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1136])).

tff(c_1141,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_1138])).

tff(c_1145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1141])).

tff(c_1147,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1136])).

tff(c_1149,plain,(
    ! [A_289,B_290,C_291,D_292] :
      ( v1_funct_2(k2_tmap_1(A_289,B_290,C_291,D_292),u1_struct_0(D_292),u1_struct_0(B_290))
      | ~ l1_struct_0(D_292)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_289),u1_struct_0(B_290))))
      | ~ v1_funct_2(C_291,u1_struct_0(A_289),u1_struct_0(B_290))
      | ~ v1_funct_1(C_291)
      | ~ l1_struct_0(B_290)
      | ~ l1_struct_0(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1151,plain,(
    ! [D_292] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_292),u1_struct_0(D_292),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_292)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_1149])).

tff(c_1155,plain,(
    ! [D_293] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_293),u1_struct_0(D_293),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_293) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1137,c_1147,c_58,c_56,c_1151])).

tff(c_1022,plain,(
    ! [A_266,B_267,C_268,D_269] :
      ( v1_funct_1(k2_tmap_1(A_266,B_267,C_268,D_269))
      | ~ l1_struct_0(D_269)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_266),u1_struct_0(B_267))))
      | ~ v1_funct_2(C_268,u1_struct_0(A_266),u1_struct_0(B_267))
      | ~ v1_funct_1(C_268)
      | ~ l1_struct_0(B_267)
      | ~ l1_struct_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1024,plain,(
    ! [D_269] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_269))
      | ~ l1_struct_0(D_269)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_1022])).

tff(c_1027,plain,(
    ! [D_269] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_269))
      | ~ l1_struct_0(D_269)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1024])).

tff(c_1034,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1027])).

tff(c_1037,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_1034])).

tff(c_1041,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1037])).

tff(c_1043,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1027])).

tff(c_1028,plain,(
    ! [A_270,B_271,C_272,D_273] :
      ( v1_funct_2(k2_tmap_1(A_270,B_271,C_272,D_273),u1_struct_0(D_273),u1_struct_0(B_271))
      | ~ l1_struct_0(D_273)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_270),u1_struct_0(B_271))))
      | ~ v1_funct_2(C_272,u1_struct_0(A_270),u1_struct_0(B_271))
      | ~ v1_funct_1(C_272)
      | ~ l1_struct_0(B_271)
      | ~ l1_struct_0(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1030,plain,(
    ! [D_273] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_273),u1_struct_0(D_273),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_273)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_1028])).

tff(c_1033,plain,(
    ! [D_273] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_273),u1_struct_0(D_273),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_273)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1030])).

tff(c_1045,plain,(
    ! [D_273] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_273),u1_struct_0(D_273),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_273)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1043,c_1033])).

tff(c_1046,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1045])).

tff(c_1049,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_1046])).

tff(c_1053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1049])).

tff(c_1059,plain,(
    ! [D_275] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_275),u1_struct_0(D_275),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_275) ) ),
    inference(splitRight,[status(thm)],[c_1045])).

tff(c_914,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( v1_funct_1(k2_tmap_1(A_244,B_245,C_246,D_247))
      | ~ l1_struct_0(D_247)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_244),u1_struct_0(B_245))))
      | ~ v1_funct_2(C_246,u1_struct_0(A_244),u1_struct_0(B_245))
      | ~ v1_funct_1(C_246)
      | ~ l1_struct_0(B_245)
      | ~ l1_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_916,plain,(
    ! [D_247] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_247))
      | ~ l1_struct_0(D_247)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_914])).

tff(c_919,plain,(
    ! [D_247] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_247))
      | ~ l1_struct_0(D_247)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_916])).

tff(c_920,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_919])).

tff(c_923,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_920])).

tff(c_927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_923])).

tff(c_929,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_919])).

tff(c_928,plain,(
    ! [D_247] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_247))
      | ~ l1_struct_0(D_247) ) ),
    inference(splitRight,[status(thm)],[c_919])).

tff(c_936,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_928])).

tff(c_939,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_936])).

tff(c_943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_939])).

tff(c_945,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_928])).

tff(c_950,plain,(
    ! [A_254,B_255,C_256,D_257] :
      ( m1_subset_1(k2_tmap_1(A_254,B_255,C_256,D_257),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_257),u1_struct_0(B_255))))
      | ~ l1_struct_0(D_257)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_254),u1_struct_0(B_255))))
      | ~ v1_funct_2(C_256,u1_struct_0(A_254),u1_struct_0(B_255))
      | ~ v1_funct_1(C_256)
      | ~ l1_struct_0(B_255)
      | ~ l1_struct_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_783,plain,(
    ! [A_220,B_221,C_222,D_223] :
      ( v1_funct_1(k2_tmap_1(A_220,B_221,C_222,D_223))
      | ~ l1_struct_0(D_223)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_220),u1_struct_0(B_221))))
      | ~ v1_funct_2(C_222,u1_struct_0(A_220),u1_struct_0(B_221))
      | ~ v1_funct_1(C_222)
      | ~ l1_struct_0(B_221)
      | ~ l1_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_787,plain,(
    ! [D_223] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_223))
      | ~ l1_struct_0(D_223)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_783])).

tff(c_793,plain,(
    ! [D_223] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_223))
      | ~ l1_struct_0(D_223)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_787])).

tff(c_794,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_793])).

tff(c_797,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_794])).

tff(c_801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_797])).

tff(c_803,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_793])).

tff(c_802,plain,(
    ! [D_223] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_223))
      | ~ l1_struct_0(D_223) ) ),
    inference(splitRight,[status(thm)],[c_793])).

tff(c_804,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_802])).

tff(c_807,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_804])).

tff(c_811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_807])).

tff(c_813,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_802])).

tff(c_843,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( m1_subset_1(k2_tmap_1(A_232,B_233,C_234,D_235),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_235),u1_struct_0(B_233))))
      | ~ l1_struct_0(D_235)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_232),u1_struct_0(B_233))))
      | ~ v1_funct_2(C_234,u1_struct_0(A_232),u1_struct_0(B_233))
      | ~ v1_funct_1(C_234)
      | ~ l1_struct_0(B_233)
      | ~ l1_struct_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_68,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_50,plain,(
    v1_tsep_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_44,plain,(
    v1_tsep_1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_38,plain,(
    ! [A_43,B_47,C_49] :
      ( r4_tsep_1(A_43,B_47,C_49)
      | ~ m1_pre_topc(C_49,A_43)
      | ~ v1_tsep_1(C_49,A_43)
      | ~ m1_pre_topc(B_47,A_43)
      | ~ v1_tsep_1(B_47,A_43)
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_40,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_156,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_209,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_146,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_213,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_136,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_211,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_126,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_215,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_116,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_210,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_106,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_214,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_96,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_212,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_86,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_216,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_72,plain,
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
    inference(cnfTransformation,[status(thm)],[f_216])).

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
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_72])).

tff(c_180,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_170])).

tff(c_190,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_180])).

tff(c_400,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_213,c_211,c_215,c_210,c_214,c_212,c_216,c_190])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_689,plain,(
    ! [A_207,B_209,C_210,E_208,D_206] :
      ( v5_pre_topc(C_210,A_207,B_209)
      | ~ m1_subset_1(k2_tmap_1(A_207,B_209,C_210,E_208),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E_208),u1_struct_0(B_209))))
      | ~ v5_pre_topc(k2_tmap_1(A_207,B_209,C_210,E_208),E_208,B_209)
      | ~ v1_funct_2(k2_tmap_1(A_207,B_209,C_210,E_208),u1_struct_0(E_208),u1_struct_0(B_209))
      | ~ v1_funct_1(k2_tmap_1(A_207,B_209,C_210,E_208))
      | ~ m1_subset_1(k2_tmap_1(A_207,B_209,C_210,D_206),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_206),u1_struct_0(B_209))))
      | ~ v5_pre_topc(k2_tmap_1(A_207,B_209,C_210,D_206),D_206,B_209)
      | ~ v1_funct_2(k2_tmap_1(A_207,B_209,C_210,D_206),u1_struct_0(D_206),u1_struct_0(B_209))
      | ~ v1_funct_1(k2_tmap_1(A_207,B_209,C_210,D_206))
      | ~ r4_tsep_1(A_207,D_206,E_208)
      | k1_tsep_1(A_207,D_206,E_208) != A_207
      | ~ m1_pre_topc(E_208,A_207)
      | v2_struct_0(E_208)
      | ~ m1_pre_topc(D_206,A_207)
      | v2_struct_0(D_206)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207),u1_struct_0(B_209))))
      | ~ v1_funct_2(C_210,u1_struct_0(A_207),u1_struct_0(B_209))
      | ~ v1_funct_1(C_210)
      | ~ l1_pre_topc(B_209)
      | ~ v2_pre_topc(B_209)
      | v2_struct_0(B_209)
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_693,plain,(
    ! [D_206] :
      ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_206),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_206),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_206),D_206,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_206),u1_struct_0(D_206),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_206))
      | ~ r4_tsep_1('#skF_1',D_206,'#skF_5')
      | k1_tsep_1('#skF_1',D_206,'#skF_5') != '#skF_1'
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(D_206,'#skF_1')
      | v2_struct_0(D_206)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_216,c_689])).

tff(c_699,plain,(
    ! [D_206] :
      ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_206),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_206),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_206),D_206,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_206),u1_struct_0(D_206),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_206))
      | ~ r4_tsep_1('#skF_1',D_206,'#skF_5')
      | k1_tsep_1('#skF_1',D_206,'#skF_5') != '#skF_1'
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(D_206,'#skF_1')
      | v2_struct_0(D_206)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_60,c_58,c_56,c_54,c_42,c_210,c_214,c_212,c_693])).

tff(c_705,plain,(
    ! [D_211] :
      ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_211),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_211),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_211),D_211,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_211),u1_struct_0(D_211),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_211))
      | ~ r4_tsep_1('#skF_1',D_211,'#skF_5')
      | k1_tsep_1('#skF_1',D_211,'#skF_5') != '#skF_1'
      | ~ m1_pre_topc(D_211,'#skF_1')
      | v2_struct_0(D_211) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_46,c_400,c_699])).

tff(c_715,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | k1_tsep_1('#skF_1','#skF_4','#skF_5') != '#skF_1'
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_215,c_705])).

tff(c_725,plain,
    ( ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_209,c_213,c_211,c_715])).

tff(c_726,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_725])).

tff(c_729,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_tsep_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_726])).

tff(c_732,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_50,c_48,c_44,c_42,c_729])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_732])).

tff(c_736,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_850,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_843,c_736])).

tff(c_855,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_813,c_58,c_56,c_54,c_850])).

tff(c_858,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_855])).

tff(c_862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_858])).

tff(c_864,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_957,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_950,c_864])).

tff(c_962,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_945,c_58,c_56,c_54,c_957])).

tff(c_965,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_962])).

tff(c_969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_965])).

tff(c_971,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_1063,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1059,c_971])).

tff(c_1066,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1063])).

tff(c_1070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_1066])).

tff(c_1072,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_1159,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1155,c_1072])).

tff(c_1169,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1159])).

tff(c_1173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_1169])).

tff(c_1175,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1174,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1292,plain,(
    ! [B_350,A_348,C_351,D_347,E_349] :
      ( v5_pre_topc(k2_tmap_1(A_348,B_350,C_351,E_349),E_349,B_350)
      | ~ v5_pre_topc(C_351,A_348,B_350)
      | ~ r4_tsep_1(A_348,D_347,E_349)
      | k1_tsep_1(A_348,D_347,E_349) != A_348
      | ~ m1_pre_topc(E_349,A_348)
      | v2_struct_0(E_349)
      | ~ m1_pre_topc(D_347,A_348)
      | v2_struct_0(D_347)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_348),u1_struct_0(B_350))))
      | ~ v1_funct_2(C_351,u1_struct_0(A_348),u1_struct_0(B_350))
      | ~ v1_funct_1(C_351)
      | ~ l1_pre_topc(B_350)
      | ~ v2_pre_topc(B_350)
      | v2_struct_0(B_350)
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348)
      | v2_struct_0(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1403,plain,(
    ! [B_386,C_389,C_390,A_388,B_387] :
      ( v5_pre_topc(k2_tmap_1(A_388,B_387,C_389,C_390),C_390,B_387)
      | ~ v5_pre_topc(C_389,A_388,B_387)
      | k1_tsep_1(A_388,B_386,C_390) != A_388
      | v2_struct_0(C_390)
      | v2_struct_0(B_386)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_388),u1_struct_0(B_387))))
      | ~ v1_funct_2(C_389,u1_struct_0(A_388),u1_struct_0(B_387))
      | ~ v1_funct_1(C_389)
      | ~ l1_pre_topc(B_387)
      | ~ v2_pre_topc(B_387)
      | v2_struct_0(B_387)
      | ~ m1_pre_topc(C_390,A_388)
      | ~ v1_tsep_1(C_390,A_388)
      | ~ m1_pre_topc(B_386,A_388)
      | ~ v1_tsep_1(B_386,A_388)
      | ~ l1_pre_topc(A_388)
      | ~ v2_pre_topc(A_388)
      | v2_struct_0(A_388) ) ),
    inference(resolution,[status(thm)],[c_38,c_1292])).

tff(c_1407,plain,(
    ! [B_387,C_389] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_387,C_389,'#skF_5'),'#skF_5',B_387)
      | ~ v5_pre_topc(C_389,'#skF_1',B_387)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_387))))
      | ~ v1_funct_2(C_389,u1_struct_0('#skF_1'),u1_struct_0(B_387))
      | ~ v1_funct_1(C_389)
      | ~ l1_pre_topc(B_387)
      | ~ v2_pre_topc(B_387)
      | v2_struct_0(B_387)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | ~ v1_tsep_1('#skF_5','#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ v1_tsep_1('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1403])).

tff(c_1414,plain,(
    ! [B_387,C_389] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_387,C_389,'#skF_5'),'#skF_5',B_387)
      | ~ v5_pre_topc(C_389,'#skF_1',B_387)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_387))))
      | ~ v1_funct_2(C_389,u1_struct_0('#skF_1'),u1_struct_0(B_387))
      | ~ v1_funct_1(C_389)
      | ~ l1_pre_topc(B_387)
      | ~ v2_pre_topc(B_387)
      | v2_struct_0(B_387)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_50,c_48,c_44,c_42,c_1407])).

tff(c_1416,plain,(
    ! [B_391,C_392] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_391,C_392,'#skF_5'),'#skF_5',B_391)
      | ~ v5_pre_topc(C_392,'#skF_1',B_391)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_391))))
      | ~ v1_funct_2(C_392,u1_struct_0('#skF_1'),u1_struct_0(B_391))
      | ~ v1_funct_1(C_392)
      | ~ l1_pre_topc(B_391)
      | ~ v2_pre_topc(B_391)
      | v2_struct_0(B_391) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_52,c_46,c_1414])).

tff(c_1421,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1416])).

tff(c_1427,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_1174,c_1421])).

tff(c_1429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1175,c_1427])).

tff(c_1431,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_1430,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_1437,plain,(
    ! [A_393,C_394,B_395] :
      ( k1_tsep_1(A_393,C_394,B_395) = k1_tsep_1(A_393,B_395,C_394)
      | ~ m1_pre_topc(C_394,A_393)
      | v2_struct_0(C_394)
      | ~ m1_pre_topc(B_395,A_393)
      | v2_struct_0(B_395)
      | ~ l1_pre_topc(A_393)
      | v2_struct_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1439,plain,(
    ! [B_395] :
      ( k1_tsep_1('#skF_1',B_395,'#skF_4') = k1_tsep_1('#skF_1','#skF_4',B_395)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_395,'#skF_1')
      | v2_struct_0(B_395)
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_1437])).

tff(c_1444,plain,(
    ! [B_395] :
      ( k1_tsep_1('#skF_1',B_395,'#skF_4') = k1_tsep_1('#skF_1','#skF_4',B_395)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_395,'#skF_1')
      | v2_struct_0(B_395)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1439])).

tff(c_1450,plain,(
    ! [B_396] :
      ( k1_tsep_1('#skF_1',B_396,'#skF_4') = k1_tsep_1('#skF_1','#skF_4',B_396)
      | ~ m1_pre_topc(B_396,'#skF_1')
      | v2_struct_0(B_396) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_52,c_1444])).

tff(c_1456,plain,
    ( k1_tsep_1('#skF_1','#skF_5','#skF_4') = k1_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1450])).

tff(c_1462,plain,
    ( k1_tsep_1('#skF_1','#skF_5','#skF_4') = '#skF_1'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1456])).

tff(c_1463,plain,(
    k1_tsep_1('#skF_1','#skF_5','#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1462])).

tff(c_1549,plain,(
    ! [C_446,A_443,B_445,E_444,D_442] :
      ( v5_pre_topc(k2_tmap_1(A_443,B_445,C_446,E_444),E_444,B_445)
      | ~ v5_pre_topc(C_446,A_443,B_445)
      | ~ r4_tsep_1(A_443,D_442,E_444)
      | k1_tsep_1(A_443,D_442,E_444) != A_443
      | ~ m1_pre_topc(E_444,A_443)
      | v2_struct_0(E_444)
      | ~ m1_pre_topc(D_442,A_443)
      | v2_struct_0(D_442)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_443),u1_struct_0(B_445))))
      | ~ v1_funct_2(C_446,u1_struct_0(A_443),u1_struct_0(B_445))
      | ~ v1_funct_1(C_446)
      | ~ l1_pre_topc(B_445)
      | ~ v2_pre_topc(B_445)
      | v2_struct_0(B_445)
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1656,plain,(
    ! [B_479,C_480,A_478,B_477,C_481] :
      ( v5_pre_topc(k2_tmap_1(A_478,B_479,C_480,C_481),C_481,B_479)
      | ~ v5_pre_topc(C_480,A_478,B_479)
      | k1_tsep_1(A_478,B_477,C_481) != A_478
      | v2_struct_0(C_481)
      | v2_struct_0(B_477)
      | ~ m1_subset_1(C_480,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_478),u1_struct_0(B_479))))
      | ~ v1_funct_2(C_480,u1_struct_0(A_478),u1_struct_0(B_479))
      | ~ v1_funct_1(C_480)
      | ~ l1_pre_topc(B_479)
      | ~ v2_pre_topc(B_479)
      | v2_struct_0(B_479)
      | ~ m1_pre_topc(C_481,A_478)
      | ~ v1_tsep_1(C_481,A_478)
      | ~ m1_pre_topc(B_477,A_478)
      | ~ v1_tsep_1(B_477,A_478)
      | ~ l1_pre_topc(A_478)
      | ~ v2_pre_topc(A_478)
      | v2_struct_0(A_478) ) ),
    inference(resolution,[status(thm)],[c_38,c_1549])).

tff(c_1658,plain,(
    ! [B_479,C_480] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_479,C_480,'#skF_4'),'#skF_4',B_479)
      | ~ v5_pre_topc(C_480,'#skF_1',B_479)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_480,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_479))))
      | ~ v1_funct_2(C_480,u1_struct_0('#skF_1'),u1_struct_0(B_479))
      | ~ v1_funct_1(C_480)
      | ~ l1_pre_topc(B_479)
      | ~ v2_pre_topc(B_479)
      | v2_struct_0(B_479)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ v1_tsep_1('#skF_4','#skF_1')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | ~ v1_tsep_1('#skF_5','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1463,c_1656])).

tff(c_1663,plain,(
    ! [B_479,C_480] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_479,C_480,'#skF_4'),'#skF_4',B_479)
      | ~ v5_pre_topc(C_480,'#skF_1',B_479)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(C_480,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_479))))
      | ~ v1_funct_2(C_480,u1_struct_0('#skF_1'),u1_struct_0(B_479))
      | ~ v1_funct_1(C_480)
      | ~ l1_pre_topc(B_479)
      | ~ v2_pre_topc(B_479)
      | v2_struct_0(B_479)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_44,c_42,c_50,c_48,c_1658])).

tff(c_1682,plain,(
    ! [B_484,C_485] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_484,C_485,'#skF_4'),'#skF_4',B_484)
      | ~ v5_pre_topc(C_485,'#skF_1',B_484)
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_484))))
      | ~ v1_funct_2(C_485,u1_struct_0('#skF_1'),u1_struct_0(B_484))
      | ~ v1_funct_1(C_485)
      | ~ l1_pre_topc(B_484)
      | ~ v2_pre_topc(B_484)
      | v2_struct_0(B_484) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_46,c_52,c_1663])).

tff(c_1687,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1682])).

tff(c_1693,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_1430,c_1687])).

tff(c_1695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1431,c_1693])).

tff(c_1697,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_1782,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1778,c_1697])).

tff(c_1785,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1782])).

tff(c_1789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_1785])).

tff(c_1791,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_1881,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1877,c_1791])).

tff(c_1884,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1881])).

tff(c_1888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_1884])).

%------------------------------------------------------------------------------
