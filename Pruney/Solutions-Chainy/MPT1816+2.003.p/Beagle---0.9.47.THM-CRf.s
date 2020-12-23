%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:06 EST 2020

% Result     : Theorem 8.47s
% Output     : CNFRefutation 8.91s
% Verified   : 
% Statistics : Number of formulae       :  309 (2811 expanded)
%              Number of leaves         :   40 (1083 expanded)
%              Depth                    :   21
%              Number of atoms          : 1153 (27850 expanded)
%              Number of equality atoms :   52 (1221 expanded)
%              Maximal formula depth    :   29 (   5 average)
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

tff(f_248,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_125,axiom,(
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

tff(f_107,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_85,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_185,axiom,(
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

tff(c_78,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_58,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_208,plain,(
    ! [B_97,A_98] :
      ( l1_pre_topc(B_97)
      | ~ m1_pre_topc(B_97,A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_211,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_208])).

tff(c_217,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_211])).

tff(c_12,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_68,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_5137,plain,(
    ! [A_807,B_808,C_809,D_810] :
      ( v1_funct_1(k2_tmap_1(A_807,B_808,C_809,D_810))
      | ~ l1_struct_0(D_810)
      | ~ m1_subset_1(C_809,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_807),u1_struct_0(B_808))))
      | ~ v1_funct_2(C_809,u1_struct_0(A_807),u1_struct_0(B_808))
      | ~ v1_funct_1(C_809)
      | ~ l1_struct_0(B_808)
      | ~ l1_struct_0(A_807) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_5139,plain,(
    ! [D_810] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_810))
      | ~ l1_struct_0(D_810)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_5137])).

tff(c_5142,plain,(
    ! [D_810] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_810))
      | ~ l1_struct_0(D_810)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_5139])).

tff(c_5143,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5142])).

tff(c_5152,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_5143])).

tff(c_5156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5152])).

tff(c_5157,plain,(
    ! [D_810] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_810))
      | ~ l1_struct_0(D_810) ) ),
    inference(splitRight,[status(thm)],[c_5142])).

tff(c_5159,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5157])).

tff(c_5164,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_5159])).

tff(c_5168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5164])).

tff(c_5171,plain,(
    ! [D_815] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_815))
      | ~ l1_struct_0(D_815) ) ),
    inference(splitRight,[status(thm)],[c_5157])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_214,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_208])).

tff(c_220,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_214])).

tff(c_5027,plain,(
    ! [A_785,B_786,C_787,D_788] :
      ( v1_funct_1(k2_tmap_1(A_785,B_786,C_787,D_788))
      | ~ l1_struct_0(D_788)
      | ~ m1_subset_1(C_787,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_785),u1_struct_0(B_786))))
      | ~ v1_funct_2(C_787,u1_struct_0(A_785),u1_struct_0(B_786))
      | ~ v1_funct_1(C_787)
      | ~ l1_struct_0(B_786)
      | ~ l1_struct_0(A_785) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_5029,plain,(
    ! [D_788] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_788))
      | ~ l1_struct_0(D_788)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_5027])).

tff(c_5032,plain,(
    ! [D_788] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_788))
      | ~ l1_struct_0(D_788)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_5029])).

tff(c_5033,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5032])).

tff(c_5036,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_5033])).

tff(c_5040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5036])).

tff(c_5041,plain,(
    ! [D_788] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_788))
      | ~ l1_struct_0(D_788) ) ),
    inference(splitRight,[status(thm)],[c_5032])).

tff(c_5043,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5041])).

tff(c_5046,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_5043])).

tff(c_5050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5046])).

tff(c_5053,plain,(
    ! [D_789] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_789))
      | ~ l1_struct_0(D_789) ) ),
    inference(splitRight,[status(thm)],[c_5041])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_3407,plain,(
    ! [A_473,B_474,C_475,D_476] :
      ( v1_funct_1(k2_tmap_1(A_473,B_474,C_475,D_476))
      | ~ l1_struct_0(D_476)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_473),u1_struct_0(B_474))))
      | ~ v1_funct_2(C_475,u1_struct_0(A_473),u1_struct_0(B_474))
      | ~ v1_funct_1(C_475)
      | ~ l1_struct_0(B_474)
      | ~ l1_struct_0(A_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3409,plain,(
    ! [D_476] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_476))
      | ~ l1_struct_0(D_476)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_3407])).

tff(c_3412,plain,(
    ! [D_476] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_476))
      | ~ l1_struct_0(D_476)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3409])).

tff(c_3413,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3412])).

tff(c_3416,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_3413])).

tff(c_3420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3416])).

tff(c_3422,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3412])).

tff(c_3421,plain,(
    ! [D_476] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_476))
      | ~ l1_struct_0(D_476) ) ),
    inference(splitRight,[status(thm)],[c_3412])).

tff(c_3423,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3421])).

tff(c_3426,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_3423])).

tff(c_3430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3426])).

tff(c_3432,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3421])).

tff(c_3433,plain,(
    ! [A_477,B_478,C_479,D_480] :
      ( v1_funct_2(k2_tmap_1(A_477,B_478,C_479,D_480),u1_struct_0(D_480),u1_struct_0(B_478))
      | ~ l1_struct_0(D_480)
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_477),u1_struct_0(B_478))))
      | ~ v1_funct_2(C_479,u1_struct_0(A_477),u1_struct_0(B_478))
      | ~ v1_funct_1(C_479)
      | ~ l1_struct_0(B_478)
      | ~ l1_struct_0(A_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3435,plain,(
    ! [D_480] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_480),u1_struct_0(D_480),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_480)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_3433])).

tff(c_3440,plain,(
    ! [D_482] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_482),u1_struct_0(D_482),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_482) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3422,c_3432,c_70,c_68,c_3435])).

tff(c_3298,plain,(
    ! [A_442,B_443,C_444,D_445] :
      ( v1_funct_1(k2_tmap_1(A_442,B_443,C_444,D_445))
      | ~ l1_struct_0(D_445)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_442),u1_struct_0(B_443))))
      | ~ v1_funct_2(C_444,u1_struct_0(A_442),u1_struct_0(B_443))
      | ~ v1_funct_1(C_444)
      | ~ l1_struct_0(B_443)
      | ~ l1_struct_0(A_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3300,plain,(
    ! [D_445] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_445))
      | ~ l1_struct_0(D_445)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_3298])).

tff(c_3303,plain,(
    ! [D_445] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_445))
      | ~ l1_struct_0(D_445)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3300])).

tff(c_3304,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3303])).

tff(c_3313,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_3304])).

tff(c_3317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3313])).

tff(c_3319,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3303])).

tff(c_3318,plain,(
    ! [D_445] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_445))
      | ~ l1_struct_0(D_445) ) ),
    inference(splitRight,[status(thm)],[c_3303])).

tff(c_3320,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3318])).

tff(c_3323,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_3320])).

tff(c_3327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3323])).

tff(c_3329,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3318])).

tff(c_3331,plain,(
    ! [A_451,B_452,C_453,D_454] :
      ( v1_funct_2(k2_tmap_1(A_451,B_452,C_453,D_454),u1_struct_0(D_454),u1_struct_0(B_452))
      | ~ l1_struct_0(D_454)
      | ~ m1_subset_1(C_453,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_451),u1_struct_0(B_452))))
      | ~ v1_funct_2(C_453,u1_struct_0(A_451),u1_struct_0(B_452))
      | ~ v1_funct_1(C_453)
      | ~ l1_struct_0(B_452)
      | ~ l1_struct_0(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3333,plain,(
    ! [D_454] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_454),u1_struct_0(D_454),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_454)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_3331])).

tff(c_3337,plain,(
    ! [D_455] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_455),u1_struct_0(D_455),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_455) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3319,c_3329,c_70,c_68,c_3333])).

tff(c_3170,plain,(
    ! [A_411,B_412,C_413,D_414] :
      ( v1_funct_1(k2_tmap_1(A_411,B_412,C_413,D_414))
      | ~ l1_struct_0(D_414)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_411),u1_struct_0(B_412))))
      | ~ v1_funct_2(C_413,u1_struct_0(A_411),u1_struct_0(B_412))
      | ~ v1_funct_1(C_413)
      | ~ l1_struct_0(B_412)
      | ~ l1_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3172,plain,(
    ! [D_414] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_414))
      | ~ l1_struct_0(D_414)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_3170])).

tff(c_3175,plain,(
    ! [D_414] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_414))
      | ~ l1_struct_0(D_414)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3172])).

tff(c_3176,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3175])).

tff(c_3179,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_3176])).

tff(c_3183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3179])).

tff(c_3185,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3175])).

tff(c_3184,plain,(
    ! [D_414] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_414))
      | ~ l1_struct_0(D_414) ) ),
    inference(splitRight,[status(thm)],[c_3175])).

tff(c_3186,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3184])).

tff(c_3189,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_3186])).

tff(c_3193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3189])).

tff(c_3195,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3184])).

tff(c_3204,plain,(
    ! [A_421,B_422,C_423,D_424] :
      ( m1_subset_1(k2_tmap_1(A_421,B_422,C_423,D_424),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_424),u1_struct_0(B_422))))
      | ~ l1_struct_0(D_424)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_421),u1_struct_0(B_422))))
      | ~ v1_funct_2(C_423,u1_struct_0(A_421),u1_struct_0(B_422))
      | ~ v1_funct_1(C_423)
      | ~ l1_struct_0(B_422)
      | ~ l1_struct_0(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3020,plain,(
    ! [A_379,B_380,C_381,D_382] :
      ( v1_funct_1(k2_tmap_1(A_379,B_380,C_381,D_382))
      | ~ l1_struct_0(D_382)
      | ~ m1_subset_1(C_381,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_379),u1_struct_0(B_380))))
      | ~ v1_funct_2(C_381,u1_struct_0(A_379),u1_struct_0(B_380))
      | ~ v1_funct_1(C_381)
      | ~ l1_struct_0(B_380)
      | ~ l1_struct_0(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3024,plain,(
    ! [D_382] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_382))
      | ~ l1_struct_0(D_382)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_3020])).

tff(c_3030,plain,(
    ! [D_382] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_382))
      | ~ l1_struct_0(D_382)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3024])).

tff(c_3031,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3030])).

tff(c_3034,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_3031])).

tff(c_3038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3034])).

tff(c_3040,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3030])).

tff(c_3039,plain,(
    ! [D_382] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_382))
      | ~ l1_struct_0(D_382) ) ),
    inference(splitRight,[status(thm)],[c_3030])).

tff(c_3052,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3039])).

tff(c_3055,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_3052])).

tff(c_3059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3055])).

tff(c_3061,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3039])).

tff(c_3079,plain,(
    ! [A_390,B_391,C_392,D_393] :
      ( m1_subset_1(k2_tmap_1(A_390,B_391,C_392,D_393),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_393),u1_struct_0(B_391))))
      | ~ l1_struct_0(D_393)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_390),u1_struct_0(B_391))))
      | ~ v1_funct_2(C_392,u1_struct_0(A_390),u1_struct_0(B_391))
      | ~ v1_funct_1(C_392)
      | ~ l1_struct_0(B_391)
      | ~ l1_struct_0(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_168,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_248,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_158,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_251,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_148,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_250,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_138,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_253,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_128,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_237,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_118,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_252,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_108,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_249,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_98,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_276,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_84,plain,
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
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_182,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_84])).

tff(c_192,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_182])).

tff(c_202,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_192])).

tff(c_600,plain,(
    ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_251,c_250,c_253,c_237,c_252,c_249,c_276,c_202])).

tff(c_54,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_56,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_356,plain,(
    ! [A_123,B_124,C_125] :
      ( m1_pre_topc(k1_tsep_1(A_123,B_124,C_125),A_123)
      | ~ m1_pre_topc(C_125,A_123)
      | v2_struct_0(C_125)
      | ~ m1_pre_topc(B_124,A_123)
      | v2_struct_0(B_124)
      | ~ l1_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_362,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_356])).

tff(c_365,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_62,c_58,c_362])).

tff(c_366,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_64,c_60,c_365])).

tff(c_80,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_299,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k2_partfun1(A_110,B_111,C_112,D_113) = k7_relat_1(C_112,D_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_305,plain,(
    ! [D_113] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_113) = k7_relat_1('#skF_3',D_113)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_299])).

tff(c_314,plain,(
    ! [D_113] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_113) = k7_relat_1('#skF_3',D_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_305])).

tff(c_511,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( k2_partfun1(u1_struct_0(A_153),u1_struct_0(B_154),C_155,u1_struct_0(D_156)) = k2_tmap_1(A_153,B_154,C_155,D_156)
      | ~ m1_pre_topc(D_156,A_153)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_153),u1_struct_0(B_154))))
      | ~ v1_funct_2(C_155,u1_struct_0(A_153),u1_struct_0(B_154))
      | ~ v1_funct_1(C_155)
      | ~ l1_pre_topc(B_154)
      | ~ v2_pre_topc(B_154)
      | v2_struct_0(B_154)
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_519,plain,(
    ! [D_156] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_156)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_156)
      | ~ m1_pre_topc(D_156,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_511])).

tff(c_531,plain,(
    ! [D_156] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_156)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_156)
      | ~ m1_pre_topc(D_156,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_70,c_68,c_314,c_519])).

tff(c_533,plain,(
    ! [D_157] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_157)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_157)
      | ~ m1_pre_topc(D_157,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_531])).

tff(c_4,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_225,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_232,plain,(
    ! [C_107,A_108,B_109] :
      ( v4_relat_1(C_107,A_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_236,plain,(
    v4_relat_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_232])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_240,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_236,c_2])).

tff(c_243,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_240])).

tff(c_539,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_243])).

tff(c_548,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_539])).

tff(c_2355,plain,(
    ! [D_344,B_347,C_346,E_348,A_345] :
      ( v5_pre_topc(k2_tmap_1(A_345,B_347,E_348,k1_tsep_1(A_345,C_346,D_344)),k1_tsep_1(A_345,C_346,D_344),B_347)
      | ~ m1_subset_1(k2_tmap_1(A_345,B_347,E_348,D_344),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_344),u1_struct_0(B_347))))
      | ~ v5_pre_topc(k2_tmap_1(A_345,B_347,E_348,D_344),D_344,B_347)
      | ~ v1_funct_2(k2_tmap_1(A_345,B_347,E_348,D_344),u1_struct_0(D_344),u1_struct_0(B_347))
      | ~ v1_funct_1(k2_tmap_1(A_345,B_347,E_348,D_344))
      | ~ m1_subset_1(k2_tmap_1(A_345,B_347,E_348,C_346),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346),u1_struct_0(B_347))))
      | ~ v5_pre_topc(k2_tmap_1(A_345,B_347,E_348,C_346),C_346,B_347)
      | ~ v1_funct_2(k2_tmap_1(A_345,B_347,E_348,C_346),u1_struct_0(C_346),u1_struct_0(B_347))
      | ~ v1_funct_1(k2_tmap_1(A_345,B_347,E_348,C_346))
      | ~ m1_subset_1(E_348,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_345),u1_struct_0(B_347))))
      | ~ v1_funct_2(E_348,u1_struct_0(A_345),u1_struct_0(B_347))
      | ~ v1_funct_1(E_348)
      | ~ r4_tsep_1(A_345,C_346,D_344)
      | ~ m1_pre_topc(D_344,A_345)
      | v2_struct_0(D_344)
      | ~ m1_pre_topc(C_346,A_345)
      | v2_struct_0(C_346)
      | ~ l1_pre_topc(B_347)
      | ~ v2_pre_topc(B_347)
      | v2_struct_0(B_347)
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_2365,plain,(
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
    inference(resolution,[status(thm)],[c_276,c_2355])).

tff(c_2380,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_58,c_70,c_68,c_66,c_237,c_252,c_249,c_2365])).

tff(c_2922,plain,(
    ! [C_360] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_360,'#skF_5')),k1_tsep_1('#skF_1',C_360,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360),C_360,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360),u1_struct_0(C_360),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_360))
      | ~ r4_tsep_1('#skF_1',C_360,'#skF_5')
      | ~ m1_pre_topc(C_360,'#skF_1')
      | v2_struct_0(C_360) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_60,c_2380])).

tff(c_2935,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_253,c_2922])).

tff(c_2948,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54,c_248,c_251,c_250,c_548,c_56,c_56,c_2935])).

tff(c_2950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_600,c_2948])).

tff(c_2952,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_3088,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3079,c_2952])).

tff(c_3103,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3040,c_3061,c_70,c_68,c_66,c_3088])).

tff(c_3109,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_3103])).

tff(c_3113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_3109])).

tff(c_3115,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_3213,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3204,c_3115])).

tff(c_3228,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3185,c_3195,c_70,c_68,c_66,c_3213])).

tff(c_3234,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3228])).

tff(c_3238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_3234])).

tff(c_3240,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_3341,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3337,c_3240])).

tff(c_3344,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_3341])).

tff(c_3348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_3344])).

tff(c_3350,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_3444,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3440,c_3350])).

tff(c_3447,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3444])).

tff(c_3451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_3447])).

tff(c_3453,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_3489,plain,(
    ! [A_494,B_495,C_496] :
      ( m1_pre_topc(k1_tsep_1(A_494,B_495,C_496),A_494)
      | ~ m1_pre_topc(C_496,A_494)
      | v2_struct_0(C_496)
      | ~ m1_pre_topc(B_495,A_494)
      | v2_struct_0(B_495)
      | ~ l1_pre_topc(A_494)
      | v2_struct_0(A_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3495,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_3489])).

tff(c_3498,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_62,c_58,c_3495])).

tff(c_3499,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_64,c_60,c_3498])).

tff(c_3457,plain,(
    ! [A_483,B_484,C_485,D_486] :
      ( k2_partfun1(A_483,B_484,C_485,D_486) = k7_relat_1(C_485,D_486)
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(A_483,B_484)))
      | ~ v1_funct_1(C_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3459,plain,(
    ! [D_486] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_486) = k7_relat_1('#skF_3',D_486)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_3457])).

tff(c_3462,plain,(
    ! [D_486] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_486) = k7_relat_1('#skF_3',D_486) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3459])).

tff(c_3612,plain,(
    ! [A_530,B_531,C_532,D_533] :
      ( k2_partfun1(u1_struct_0(A_530),u1_struct_0(B_531),C_532,u1_struct_0(D_533)) = k2_tmap_1(A_530,B_531,C_532,D_533)
      | ~ m1_pre_topc(D_533,A_530)
      | ~ m1_subset_1(C_532,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_530),u1_struct_0(B_531))))
      | ~ v1_funct_2(C_532,u1_struct_0(A_530),u1_struct_0(B_531))
      | ~ v1_funct_1(C_532)
      | ~ l1_pre_topc(B_531)
      | ~ v2_pre_topc(B_531)
      | v2_struct_0(B_531)
      | ~ l1_pre_topc(A_530)
      | ~ v2_pre_topc(A_530)
      | v2_struct_0(A_530) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3616,plain,(
    ! [D_533] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_533)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_533)
      | ~ m1_pre_topc(D_533,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_3612])).

tff(c_3620,plain,(
    ! [D_533] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_533)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_533)
      | ~ m1_pre_topc(D_533,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_70,c_68,c_3462,c_3616])).

tff(c_3622,plain,(
    ! [D_534] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_534)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_534)
      | ~ m1_pre_topc(D_534,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_3620])).

tff(c_3628,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3622,c_243])).

tff(c_3637,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3628])).

tff(c_3452,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_3852,plain,(
    ! [C_582,A_581,B_583,D_580,E_584] :
      ( v5_pre_topc(k2_tmap_1(A_581,B_583,E_584,C_582),C_582,B_583)
      | ~ m1_subset_1(k2_tmap_1(A_581,B_583,E_584,k1_tsep_1(A_581,C_582,D_580)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_581,C_582,D_580)),u1_struct_0(B_583))))
      | ~ v5_pre_topc(k2_tmap_1(A_581,B_583,E_584,k1_tsep_1(A_581,C_582,D_580)),k1_tsep_1(A_581,C_582,D_580),B_583)
      | ~ v1_funct_2(k2_tmap_1(A_581,B_583,E_584,k1_tsep_1(A_581,C_582,D_580)),u1_struct_0(k1_tsep_1(A_581,C_582,D_580)),u1_struct_0(B_583))
      | ~ v1_funct_1(k2_tmap_1(A_581,B_583,E_584,k1_tsep_1(A_581,C_582,D_580)))
      | ~ m1_subset_1(E_584,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_581),u1_struct_0(B_583))))
      | ~ v1_funct_2(E_584,u1_struct_0(A_581),u1_struct_0(B_583))
      | ~ v1_funct_1(E_584)
      | ~ r4_tsep_1(A_581,C_582,D_580)
      | ~ m1_pre_topc(D_580,A_581)
      | v2_struct_0(D_580)
      | ~ m1_pre_topc(C_582,A_581)
      | v2_struct_0(C_582)
      | ~ l1_pre_topc(B_583)
      | ~ v2_pre_topc(B_583)
      | v2_struct_0(B_583)
      | ~ l1_pre_topc(A_581)
      | ~ v2_pre_topc(A_581)
      | v2_struct_0(A_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_3859,plain,(
    ! [B_583,E_584] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_583,E_584,'#skF_4'),'#skF_4',B_583)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_583,E_584,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_583))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_583,E_584,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_583)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_583,E_584,k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_583))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_583,E_584,k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_584,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_583))))
      | ~ v1_funct_2(E_584,u1_struct_0('#skF_1'),u1_struct_0(B_583))
      | ~ v1_funct_1(E_584)
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
    inference(superposition,[status(thm),theory(equality)],[c_56,c_3852])).

tff(c_3865,plain,(
    ! [B_583,E_584] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_583,E_584,'#skF_4'),'#skF_4',B_583)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_583,E_584,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_583))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_583,E_584,'#skF_1'),'#skF_1',B_583)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_583,E_584,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_583))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_583,E_584,'#skF_1'))
      | ~ m1_subset_1(E_584,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_583))))
      | ~ v1_funct_2(E_584,u1_struct_0('#skF_1'),u1_struct_0(B_583))
      | ~ v1_funct_1(E_584)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_583)
      | ~ v2_pre_topc(B_583)
      | v2_struct_0(B_583)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_62,c_58,c_54,c_56,c_56,c_56,c_56,c_56,c_56,c_3859])).

tff(c_4002,plain,(
    ! [B_610,E_611] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_610,E_611,'#skF_4'),'#skF_4',B_610)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_610,E_611,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_610))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_610,E_611,'#skF_1'),'#skF_1',B_610)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_610,E_611,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_610))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_610,E_611,'#skF_1'))
      | ~ m1_subset_1(E_611,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_610))))
      | ~ v1_funct_2(E_611,u1_struct_0('#skF_1'),u1_struct_0(B_610))
      | ~ v1_funct_1(E_611)
      | ~ l1_pre_topc(B_610)
      | ~ v2_pre_topc(B_610)
      | v2_struct_0(B_610) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_64,c_60,c_3865])).

tff(c_4005,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_3637,c_4002])).

tff(c_4011,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_70,c_3637,c_68,c_3637,c_3452,c_3637,c_66,c_4005])).

tff(c_4013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3453,c_4011])).

tff(c_4015,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_4074,plain,(
    ! [A_629,B_630,C_631,D_632] :
      ( v1_funct_1(k2_tmap_1(A_629,B_630,C_631,D_632))
      | ~ l1_struct_0(D_632)
      | ~ m1_subset_1(C_631,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_629),u1_struct_0(B_630))))
      | ~ v1_funct_2(C_631,u1_struct_0(A_629),u1_struct_0(B_630))
      | ~ v1_funct_1(C_631)
      | ~ l1_struct_0(B_630)
      | ~ l1_struct_0(A_629) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4076,plain,(
    ! [D_632] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_632))
      | ~ l1_struct_0(D_632)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_4074])).

tff(c_4079,plain,(
    ! [D_632] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_632))
      | ~ l1_struct_0(D_632)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_4076])).

tff(c_4080,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4079])).

tff(c_4089,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_4080])).

tff(c_4093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4089])).

tff(c_4095,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4079])).

tff(c_4050,plain,(
    ! [A_623,B_624,C_625] :
      ( m1_pre_topc(k1_tsep_1(A_623,B_624,C_625),A_623)
      | ~ m1_pre_topc(C_625,A_623)
      | v2_struct_0(C_625)
      | ~ m1_pre_topc(B_624,A_623)
      | v2_struct_0(B_624)
      | ~ l1_pre_topc(A_623)
      | v2_struct_0(A_623) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4056,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4050])).

tff(c_4059,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_62,c_58,c_4056])).

tff(c_4060,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_64,c_60,c_4059])).

tff(c_4020,plain,(
    ! [A_612,B_613,C_614,D_615] :
      ( k2_partfun1(A_612,B_613,C_614,D_615) = k7_relat_1(C_614,D_615)
      | ~ m1_subset_1(C_614,k1_zfmisc_1(k2_zfmisc_1(A_612,B_613)))
      | ~ v1_funct_1(C_614) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4022,plain,(
    ! [D_615] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_615) = k7_relat_1('#skF_3',D_615)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_4020])).

tff(c_4025,plain,(
    ! [D_615] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_615) = k7_relat_1('#skF_3',D_615) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4022])).

tff(c_4181,plain,(
    ! [A_663,B_664,C_665,D_666] :
      ( k2_partfun1(u1_struct_0(A_663),u1_struct_0(B_664),C_665,u1_struct_0(D_666)) = k2_tmap_1(A_663,B_664,C_665,D_666)
      | ~ m1_pre_topc(D_666,A_663)
      | ~ m1_subset_1(C_665,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_663),u1_struct_0(B_664))))
      | ~ v1_funct_2(C_665,u1_struct_0(A_663),u1_struct_0(B_664))
      | ~ v1_funct_1(C_665)
      | ~ l1_pre_topc(B_664)
      | ~ v2_pre_topc(B_664)
      | v2_struct_0(B_664)
      | ~ l1_pre_topc(A_663)
      | ~ v2_pre_topc(A_663)
      | v2_struct_0(A_663) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4185,plain,(
    ! [D_666] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_666)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_666)
      | ~ m1_pre_topc(D_666,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_4181])).

tff(c_4189,plain,(
    ! [D_666] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_666)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_666)
      | ~ m1_pre_topc(D_666,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_70,c_68,c_4025,c_4185])).

tff(c_4191,plain,(
    ! [D_667] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_667)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_667)
      | ~ m1_pre_topc(D_667,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_4189])).

tff(c_4197,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4191,c_243])).

tff(c_4206,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4060,c_4197])).

tff(c_4014,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_4094,plain,(
    ! [D_632] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_632))
      | ~ l1_struct_0(D_632) ) ),
    inference(splitRight,[status(thm)],[c_4079])).

tff(c_4096,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4094])).

tff(c_4101,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_4096])).

tff(c_4105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4101])).

tff(c_4106,plain,(
    ! [D_632] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_632))
      | ~ l1_struct_0(D_632) ) ),
    inference(splitRight,[status(thm)],[c_4094])).

tff(c_4107,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4094])).

tff(c_4109,plain,(
    ! [A_638,B_639,C_640,D_641] :
      ( v1_funct_2(k2_tmap_1(A_638,B_639,C_640,D_641),u1_struct_0(D_641),u1_struct_0(B_639))
      | ~ l1_struct_0(D_641)
      | ~ m1_subset_1(C_640,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_638),u1_struct_0(B_639))))
      | ~ v1_funct_2(C_640,u1_struct_0(A_638),u1_struct_0(B_639))
      | ~ v1_funct_1(C_640)
      | ~ l1_struct_0(B_639)
      | ~ l1_struct_0(A_638) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4111,plain,(
    ! [D_641] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641),u1_struct_0(D_641),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_641)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_4109])).

tff(c_4114,plain,(
    ! [D_641] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641),u1_struct_0(D_641),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_641) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4095,c_4107,c_70,c_68,c_4111])).

tff(c_24,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( m1_subset_1(k2_tmap_1(A_35,B_36,C_37,D_38),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_38),u1_struct_0(B_36))))
      | ~ l1_struct_0(D_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35),u1_struct_0(B_36))))
      | ~ v1_funct_2(C_37,u1_struct_0(A_35),u1_struct_0(B_36))
      | ~ v1_funct_1(C_37)
      | ~ l1_struct_0(B_36)
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4426,plain,(
    ! [D_720,A_719,B_723,D_722,C_721] :
      ( k2_partfun1(u1_struct_0(D_722),u1_struct_0(B_723),k2_tmap_1(A_719,B_723,C_721,D_722),u1_struct_0(D_720)) = k2_tmap_1(D_722,B_723,k2_tmap_1(A_719,B_723,C_721,D_722),D_720)
      | ~ m1_pre_topc(D_720,D_722)
      | ~ v1_funct_2(k2_tmap_1(A_719,B_723,C_721,D_722),u1_struct_0(D_722),u1_struct_0(B_723))
      | ~ v1_funct_1(k2_tmap_1(A_719,B_723,C_721,D_722))
      | ~ l1_pre_topc(B_723)
      | ~ v2_pre_topc(B_723)
      | v2_struct_0(B_723)
      | ~ l1_pre_topc(D_722)
      | ~ v2_pre_topc(D_722)
      | v2_struct_0(D_722)
      | ~ l1_struct_0(D_722)
      | ~ m1_subset_1(C_721,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_719),u1_struct_0(B_723))))
      | ~ v1_funct_2(C_721,u1_struct_0(A_719),u1_struct_0(B_723))
      | ~ v1_funct_1(C_721)
      | ~ l1_struct_0(B_723)
      | ~ l1_struct_0(A_719) ) ),
    inference(resolution,[status(thm)],[c_24,c_4181])).

tff(c_4430,plain,(
    ! [D_722,D_720] :
      ( k2_partfun1(u1_struct_0(D_722),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_722),u1_struct_0(D_720)) = k2_tmap_1(D_722,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_722),D_720)
      | ~ m1_pre_topc(D_720,D_722)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_722),u1_struct_0(D_722),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_722))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(D_722)
      | ~ v2_pre_topc(D_722)
      | v2_struct_0(D_722)
      | ~ l1_struct_0(D_722)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_4426])).

tff(c_4434,plain,(
    ! [D_722,D_720] :
      ( k2_partfun1(u1_struct_0(D_722),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_722),u1_struct_0(D_720)) = k2_tmap_1(D_722,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_722),D_720)
      | ~ m1_pre_topc(D_720,D_722)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_722),u1_struct_0(D_722),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_722))
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(D_722)
      | ~ v2_pre_topc(D_722)
      | v2_struct_0(D_722)
      | ~ l1_struct_0(D_722) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4095,c_4107,c_70,c_68,c_74,c_72,c_4430])).

tff(c_4454,plain,(
    ! [D_729,D_730] :
      ( k2_partfun1(u1_struct_0(D_729),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_729),u1_struct_0(D_730)) = k2_tmap_1(D_729,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_729),D_730)
      | ~ m1_pre_topc(D_730,D_729)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_729),u1_struct_0(D_729),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_729))
      | ~ l1_pre_topc(D_729)
      | ~ v2_pre_topc(D_729)
      | v2_struct_0(D_729)
      | ~ l1_struct_0(D_729) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4434])).

tff(c_4116,plain,(
    ! [A_643,B_644,C_645,D_646] :
      ( m1_subset_1(k2_tmap_1(A_643,B_644,C_645,D_646),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_646),u1_struct_0(B_644))))
      | ~ l1_struct_0(D_646)
      | ~ m1_subset_1(C_645,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_643),u1_struct_0(B_644))))
      | ~ v1_funct_2(C_645,u1_struct_0(A_643),u1_struct_0(B_644))
      | ~ v1_funct_1(C_645)
      | ~ l1_struct_0(B_644)
      | ~ l1_struct_0(A_643) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k2_partfun1(A_9,B_10,C_11,D_12) = k7_relat_1(C_11,D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4252,plain,(
    ! [D_670,D_671,C_672,B_669,A_668] :
      ( k2_partfun1(u1_struct_0(D_670),u1_struct_0(B_669),k2_tmap_1(A_668,B_669,C_672,D_670),D_671) = k7_relat_1(k2_tmap_1(A_668,B_669,C_672,D_670),D_671)
      | ~ v1_funct_1(k2_tmap_1(A_668,B_669,C_672,D_670))
      | ~ l1_struct_0(D_670)
      | ~ m1_subset_1(C_672,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_668),u1_struct_0(B_669))))
      | ~ v1_funct_2(C_672,u1_struct_0(A_668),u1_struct_0(B_669))
      | ~ v1_funct_1(C_672)
      | ~ l1_struct_0(B_669)
      | ~ l1_struct_0(A_668) ) ),
    inference(resolution,[status(thm)],[c_4116,c_10])).

tff(c_4256,plain,(
    ! [D_670,D_671] :
      ( k2_partfun1(u1_struct_0(D_670),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_670),D_671) = k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_670),D_671)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_670))
      | ~ l1_struct_0(D_670)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_4252])).

tff(c_4260,plain,(
    ! [D_670,D_671] :
      ( k2_partfun1(u1_struct_0(D_670),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_3',D_670),D_671) = k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_670),D_671)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_670))
      | ~ l1_struct_0(D_670) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4095,c_4107,c_70,c_68,c_4256])).

tff(c_4476,plain,(
    ! [D_731,D_732] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_731),u1_struct_0(D_732)) = k2_tmap_1(D_731,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_731),D_732)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_731))
      | ~ l1_struct_0(D_731)
      | ~ m1_pre_topc(D_732,D_731)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_731),u1_struct_0(D_731),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_731))
      | ~ l1_pre_topc(D_731)
      | ~ v2_pre_topc(D_731)
      | v2_struct_0(D_731)
      | ~ l1_struct_0(D_731) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4454,c_4260])).

tff(c_4485,plain,(
    ! [D_733,D_734] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_733),u1_struct_0(D_734)) = k2_tmap_1(D_733,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_733),D_734)
      | ~ m1_pre_topc(D_734,D_733)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_733))
      | ~ l1_pre_topc(D_733)
      | ~ v2_pre_topc(D_733)
      | v2_struct_0(D_733)
      | ~ l1_struct_0(D_733) ) ),
    inference(resolution,[status(thm)],[c_4114,c_4476])).

tff(c_4138,plain,(
    ! [A_647,B_648,C_649,D_650] :
      ( v1_relat_1(k2_tmap_1(A_647,B_648,C_649,D_650))
      | ~ l1_struct_0(D_650)
      | ~ m1_subset_1(C_649,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_647),u1_struct_0(B_648))))
      | ~ v1_funct_2(C_649,u1_struct_0(A_647),u1_struct_0(B_648))
      | ~ v1_funct_1(C_649)
      | ~ l1_struct_0(B_648)
      | ~ l1_struct_0(A_647) ) ),
    inference(resolution,[status(thm)],[c_4116,c_4])).

tff(c_4291,plain,(
    ! [B_686,D_684,A_682,C_683,D_685] :
      ( v1_relat_1(k2_tmap_1(D_685,B_686,k2_tmap_1(A_682,B_686,C_683,D_685),D_684))
      | ~ l1_struct_0(D_684)
      | ~ v1_funct_2(k2_tmap_1(A_682,B_686,C_683,D_685),u1_struct_0(D_685),u1_struct_0(B_686))
      | ~ v1_funct_1(k2_tmap_1(A_682,B_686,C_683,D_685))
      | ~ l1_struct_0(D_685)
      | ~ m1_subset_1(C_683,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_682),u1_struct_0(B_686))))
      | ~ v1_funct_2(C_683,u1_struct_0(A_682),u1_struct_0(B_686))
      | ~ v1_funct_1(C_683)
      | ~ l1_struct_0(B_686)
      | ~ l1_struct_0(A_682) ) ),
    inference(resolution,[status(thm)],[c_24,c_4138])).

tff(c_4295,plain,(
    ! [D_641,D_684] :
      ( v1_relat_1(k2_tmap_1(D_641,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641),D_684))
      | ~ l1_struct_0(D_684)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(D_641) ) ),
    inference(resolution,[status(thm)],[c_4114,c_4291])).

tff(c_4300,plain,(
    ! [D_641,D_684] :
      ( v1_relat_1(k2_tmap_1(D_641,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641),D_684))
      | ~ l1_struct_0(D_684)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641))
      | ~ l1_struct_0(D_641) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4095,c_4107,c_70,c_68,c_66,c_4295])).

tff(c_4589,plain,(
    ! [D_737,D_738] :
      ( v1_relat_1(k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_737),u1_struct_0(D_738)))
      | ~ l1_struct_0(D_738)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_737))
      | ~ l1_struct_0(D_737)
      | ~ m1_pre_topc(D_738,D_737)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_737))
      | ~ l1_pre_topc(D_737)
      | ~ v2_pre_topc(D_737)
      | v2_struct_0(D_737)
      | ~ l1_struct_0(D_737) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4485,c_4300])).

tff(c_4595,plain,(
    ! [D_738] :
      ( v1_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_738)))
      | ~ l1_struct_0(D_738)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
      | ~ l1_struct_0('#skF_1')
      | ~ m1_pre_topc(D_738,'#skF_1')
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4206,c_4589])).

tff(c_4600,plain,(
    ! [D_738] :
      ( v1_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_738)))
      | ~ l1_struct_0(D_738)
      | ~ m1_pre_topc(D_738,'#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4095,c_80,c_78,c_70,c_4206,c_4095,c_70,c_4206,c_4595])).

tff(c_4601,plain,(
    ! [D_738] :
      ( v1_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_738)))
      | ~ l1_struct_0(D_738)
      | ~ m1_pre_topc(D_738,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4600])).

tff(c_4190,plain,(
    ! [D_666] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_666)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_666)
      | ~ m1_pre_topc(D_666,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_4189])).

tff(c_8,plain,(
    ! [C_8,A_6,B_7] :
      ( v4_relat_1(C_8,A_6)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4148,plain,(
    ! [A_652,B_653,C_654,D_655] :
      ( v4_relat_1(k2_tmap_1(A_652,B_653,C_654,D_655),u1_struct_0(D_655))
      | ~ l1_struct_0(D_655)
      | ~ m1_subset_1(C_654,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_652),u1_struct_0(B_653))))
      | ~ v1_funct_2(C_654,u1_struct_0(A_652),u1_struct_0(B_653))
      | ~ v1_funct_1(C_654)
      | ~ l1_struct_0(B_653)
      | ~ l1_struct_0(A_652) ) ),
    inference(resolution,[status(thm)],[c_4116,c_8])).

tff(c_4341,plain,(
    ! [A_701,C_703,B_705,D_704,D_702] :
      ( v4_relat_1(k2_tmap_1(D_704,B_705,k2_tmap_1(A_701,B_705,C_703,D_704),D_702),u1_struct_0(D_702))
      | ~ l1_struct_0(D_702)
      | ~ v1_funct_2(k2_tmap_1(A_701,B_705,C_703,D_704),u1_struct_0(D_704),u1_struct_0(B_705))
      | ~ v1_funct_1(k2_tmap_1(A_701,B_705,C_703,D_704))
      | ~ l1_struct_0(D_704)
      | ~ m1_subset_1(C_703,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_701),u1_struct_0(B_705))))
      | ~ v1_funct_2(C_703,u1_struct_0(A_701),u1_struct_0(B_705))
      | ~ v1_funct_1(C_703)
      | ~ l1_struct_0(B_705)
      | ~ l1_struct_0(A_701) ) ),
    inference(resolution,[status(thm)],[c_24,c_4148])).

tff(c_4345,plain,(
    ! [D_641,D_702] :
      ( v4_relat_1(k2_tmap_1(D_641,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641),D_702),u1_struct_0(D_702))
      | ~ l1_struct_0(D_702)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(D_641) ) ),
    inference(resolution,[status(thm)],[c_4114,c_4341])).

tff(c_4350,plain,(
    ! [D_641,D_702] :
      ( v4_relat_1(k2_tmap_1(D_641,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641),D_702),u1_struct_0(D_702))
      | ~ l1_struct_0(D_702)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641))
      | ~ l1_struct_0(D_641) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4095,c_4107,c_70,c_68,c_66,c_4345])).

tff(c_4680,plain,(
    ! [D_751,D_752] :
      ( v4_relat_1(k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_751),u1_struct_0(D_752)),u1_struct_0(D_752))
      | ~ l1_struct_0(D_752)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_751))
      | ~ l1_struct_0(D_751)
      | ~ m1_pre_topc(D_752,D_751)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_751))
      | ~ l1_pre_topc(D_751)
      | ~ v2_pre_topc(D_751)
      | v2_struct_0(D_751)
      | ~ l1_struct_0(D_751) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4485,c_4350])).

tff(c_4689,plain,(
    ! [D_752] :
      ( v4_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_752)),u1_struct_0(D_752))
      | ~ l1_struct_0(D_752)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
      | ~ l1_struct_0('#skF_1')
      | ~ m1_pre_topc(D_752,'#skF_1')
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4206,c_4680])).

tff(c_4695,plain,(
    ! [D_752] :
      ( v4_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_752)),u1_struct_0(D_752))
      | ~ l1_struct_0(D_752)
      | ~ m1_pre_topc(D_752,'#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4095,c_80,c_78,c_70,c_4206,c_4095,c_70,c_4206,c_4689])).

tff(c_4697,plain,(
    ! [D_753] :
      ( v4_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_753)),u1_struct_0(D_753))
      | ~ l1_struct_0(D_753)
      | ~ m1_pre_topc(D_753,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4695])).

tff(c_4710,plain,(
    ! [D_754] :
      ( k7_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_754)),u1_struct_0(D_754)) = k7_relat_1('#skF_3',u1_struct_0(D_754))
      | ~ v1_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_754)))
      | ~ l1_struct_0(D_754)
      | ~ m1_pre_topc(D_754,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4697,c_2])).

tff(c_4727,plain,(
    ! [D_755] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_755),u1_struct_0(D_755)) = k7_relat_1('#skF_3',u1_struct_0(D_755))
      | ~ v1_relat_1(k7_relat_1('#skF_3',u1_struct_0(D_755)))
      | ~ l1_struct_0(D_755)
      | ~ m1_pre_topc(D_755,'#skF_1')
      | ~ m1_pre_topc(D_755,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4190,c_4710])).

tff(c_4737,plain,(
    ! [D_756] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_756),u1_struct_0(D_756)) = k7_relat_1('#skF_3',u1_struct_0(D_756))
      | ~ l1_struct_0(D_756)
      | ~ m1_pre_topc(D_756,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4601,c_4727])).

tff(c_4484,plain,(
    ! [D_641,D_732] :
      ( k7_relat_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641),u1_struct_0(D_732)) = k2_tmap_1(D_641,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641),D_732)
      | ~ m1_pre_topc(D_732,D_641)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_641))
      | ~ l1_pre_topc(D_641)
      | ~ v2_pre_topc(D_641)
      | v2_struct_0(D_641)
      | ~ l1_struct_0(D_641) ) ),
    inference(resolution,[status(thm)],[c_4114,c_4476])).

tff(c_4776,plain,(
    ! [D_757] :
      ( k2_tmap_1(D_757,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_757),D_757) = k7_relat_1('#skF_3',u1_struct_0(D_757))
      | ~ m1_pre_topc(D_757,D_757)
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_757))
      | ~ l1_pre_topc(D_757)
      | ~ v2_pre_topc(D_757)
      | v2_struct_0(D_757)
      | ~ l1_struct_0(D_757)
      | ~ l1_struct_0(D_757)
      | ~ m1_pre_topc(D_757,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4737,c_4484])).

tff(c_4788,plain,(
    ! [D_632] :
      ( k2_tmap_1(D_632,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_632),D_632) = k7_relat_1('#skF_3',u1_struct_0(D_632))
      | ~ m1_pre_topc(D_632,D_632)
      | ~ l1_pre_topc(D_632)
      | ~ v2_pre_topc(D_632)
      | v2_struct_0(D_632)
      | ~ m1_pre_topc(D_632,'#skF_1')
      | ~ l1_struct_0(D_632) ) ),
    inference(resolution,[status(thm)],[c_4106,c_4776])).

tff(c_4646,plain,(
    ! [E_749,D_745,A_746,C_747,B_748] :
      ( v5_pre_topc(k2_tmap_1(A_746,B_748,E_749,D_745),D_745,B_748)
      | ~ m1_subset_1(k2_tmap_1(A_746,B_748,E_749,k1_tsep_1(A_746,C_747,D_745)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_746,C_747,D_745)),u1_struct_0(B_748))))
      | ~ v5_pre_topc(k2_tmap_1(A_746,B_748,E_749,k1_tsep_1(A_746,C_747,D_745)),k1_tsep_1(A_746,C_747,D_745),B_748)
      | ~ v1_funct_2(k2_tmap_1(A_746,B_748,E_749,k1_tsep_1(A_746,C_747,D_745)),u1_struct_0(k1_tsep_1(A_746,C_747,D_745)),u1_struct_0(B_748))
      | ~ v1_funct_1(k2_tmap_1(A_746,B_748,E_749,k1_tsep_1(A_746,C_747,D_745)))
      | ~ m1_subset_1(E_749,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_746),u1_struct_0(B_748))))
      | ~ v1_funct_2(E_749,u1_struct_0(A_746),u1_struct_0(B_748))
      | ~ v1_funct_1(E_749)
      | ~ r4_tsep_1(A_746,C_747,D_745)
      | ~ m1_pre_topc(D_745,A_746)
      | v2_struct_0(D_745)
      | ~ m1_pre_topc(C_747,A_746)
      | v2_struct_0(C_747)
      | ~ l1_pre_topc(B_748)
      | ~ v2_pre_topc(B_748)
      | v2_struct_0(B_748)
      | ~ l1_pre_topc(A_746)
      | ~ v2_pre_topc(A_746)
      | v2_struct_0(A_746) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_4660,plain,(
    ! [B_748,E_749] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_748,E_749,'#skF_5'),'#skF_5',B_748)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_748,E_749,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_748))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_748,E_749,k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_748)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_748,E_749,k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_748))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_748,E_749,k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_749,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_748))))
      | ~ v1_funct_2(E_749,u1_struct_0('#skF_1'),u1_struct_0(B_748))
      | ~ v1_funct_1(E_749)
      | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_748)
      | ~ v2_pre_topc(B_748)
      | v2_struct_0(B_748)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4646])).

tff(c_4669,plain,(
    ! [B_748,E_749] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_748,E_749,'#skF_5'),'#skF_5',B_748)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_748,E_749,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_748))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_748,E_749,'#skF_1'),'#skF_1',B_748)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_748,E_749,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_748))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_748,E_749,'#skF_1'))
      | ~ m1_subset_1(E_749,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_748))))
      | ~ v1_funct_2(E_749,u1_struct_0('#skF_1'),u1_struct_0(B_748))
      | ~ v1_funct_1(E_749)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_748)
      | ~ v2_pre_topc(B_748)
      | v2_struct_0(B_748)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_62,c_58,c_54,c_56,c_56,c_56,c_56,c_56,c_56,c_4660])).

tff(c_4957,plain,(
    ! [B_769,E_770] :
      ( v5_pre_topc(k2_tmap_1('#skF_1',B_769,E_770,'#skF_5'),'#skF_5',B_769)
      | ~ m1_subset_1(k2_tmap_1('#skF_1',B_769,E_770,'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_769))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1',B_769,E_770,'#skF_1'),'#skF_1',B_769)
      | ~ v1_funct_2(k2_tmap_1('#skF_1',B_769,E_770,'#skF_1'),u1_struct_0('#skF_1'),u1_struct_0(B_769))
      | ~ v1_funct_1(k2_tmap_1('#skF_1',B_769,E_770,'#skF_1'))
      | ~ m1_subset_1(E_770,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_769))))
      | ~ v1_funct_2(E_770,u1_struct_0('#skF_1'),u1_struct_0(B_769))
      | ~ v1_funct_1(E_770)
      | ~ l1_pre_topc(B_769)
      | ~ v2_pre_topc(B_769)
      | v2_struct_0(B_769) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_64,c_60,c_4669])).

tff(c_4961,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_4788,c_4957])).

tff(c_4970,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4095,c_4060,c_80,c_78,c_4060,c_74,c_72,c_70,c_4206,c_68,c_4206,c_66,c_4206,c_70,c_4206,c_4206,c_68,c_4206,c_4206,c_4014,c_4206,c_4206,c_66,c_243,c_4206,c_4961])).

tff(c_4972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_4015,c_4970])).

tff(c_4974,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_5057,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5053,c_4974])).

tff(c_5060,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_5057])).

tff(c_5064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_5060])).

tff(c_5066,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_5175,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5171,c_5066])).

tff(c_5178,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_5175])).

tff(c_5182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_5178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:10:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.47/2.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.47/2.86  
% 8.47/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.47/2.87  %$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.47/2.87  
% 8.47/2.87  %Foreground sorts:
% 8.47/2.87  
% 8.47/2.87  
% 8.47/2.87  %Background operators:
% 8.47/2.87  
% 8.47/2.87  
% 8.47/2.87  %Foreground operators:
% 8.47/2.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.47/2.87  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 8.47/2.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.47/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.47/2.87  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.47/2.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.47/2.87  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 8.47/2.87  tff('#skF_5', type, '#skF_5': $i).
% 8.47/2.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.47/2.87  tff('#skF_2', type, '#skF_2': $i).
% 8.47/2.87  tff('#skF_3', type, '#skF_3': $i).
% 8.47/2.87  tff('#skF_1', type, '#skF_1': $i).
% 8.47/2.87  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.47/2.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.47/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.47/2.87  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.47/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.47/2.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.47/2.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.47/2.87  tff('#skF_4', type, '#skF_4': $i).
% 8.47/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.47/2.87  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 8.47/2.87  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.47/2.87  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.47/2.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.47/2.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.47/2.87  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 8.47/2.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.47/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.47/2.87  
% 8.91/2.91  tff(f_248, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (((A = k1_tsep_1(A, D, E)) & r4_tsep_1(A, D, E)) => ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, C, E))) & v1_funct_2(k2_tmap_1(A, B, C, E), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, E), E, B)) & m1_subset_1(k2_tmap_1(A, B, C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_tmap_1)).
% 8.91/2.91  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.91/2.91  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.91/2.91  tff(f_125, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 8.91/2.91  tff(f_107, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 8.91/2.91  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.91/2.91  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 8.91/2.91  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.91/2.91  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.91/2.91  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 8.91/2.91  tff(f_185, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_funct_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D))) & v1_funct_2(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_tsep_1(A, C, D), B)) & m1_subset_1(k2_tmap_1(A, B, E, k1_tsep_1(A, C, D)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k2_tmap_1(A, B, E, C)) & v1_funct_2(k2_tmap_1(A, B, E, C), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, C), C, B)) & m1_subset_1(k2_tmap_1(A, B, E, C), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k2_tmap_1(A, B, E, D))) & v1_funct_2(k2_tmap_1(A, B, E, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, E, D), D, B)) & m1_subset_1(k2_tmap_1(A, B, E, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_tmap_1)).
% 8.91/2.91  tff(c_78, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_58, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_208, plain, (![B_97, A_98]: (l1_pre_topc(B_97) | ~m1_pre_topc(B_97, A_98) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.91/2.91  tff(c_211, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_208])).
% 8.91/2.91  tff(c_217, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_211])).
% 8.91/2.91  tff(c_12, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.91/2.91  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_68, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_5137, plain, (![A_807, B_808, C_809, D_810]: (v1_funct_1(k2_tmap_1(A_807, B_808, C_809, D_810)) | ~l1_struct_0(D_810) | ~m1_subset_1(C_809, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_807), u1_struct_0(B_808)))) | ~v1_funct_2(C_809, u1_struct_0(A_807), u1_struct_0(B_808)) | ~v1_funct_1(C_809) | ~l1_struct_0(B_808) | ~l1_struct_0(A_807))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_5139, plain, (![D_810]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_810)) | ~l1_struct_0(D_810) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_5137])).
% 8.91/2.91  tff(c_5142, plain, (![D_810]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_810)) | ~l1_struct_0(D_810) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_5139])).
% 8.91/2.91  tff(c_5143, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_5142])).
% 8.91/2.91  tff(c_5152, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_5143])).
% 8.91/2.91  tff(c_5156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_5152])).
% 8.91/2.91  tff(c_5157, plain, (![D_810]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_810)) | ~l1_struct_0(D_810))), inference(splitRight, [status(thm)], [c_5142])).
% 8.91/2.91  tff(c_5159, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_5157])).
% 8.91/2.91  tff(c_5164, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_5159])).
% 8.91/2.91  tff(c_5168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_5164])).
% 8.91/2.91  tff(c_5171, plain, (![D_815]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_815)) | ~l1_struct_0(D_815))), inference(splitRight, [status(thm)], [c_5157])).
% 8.91/2.91  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_214, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_208])).
% 8.91/2.91  tff(c_220, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_214])).
% 8.91/2.91  tff(c_5027, plain, (![A_785, B_786, C_787, D_788]: (v1_funct_1(k2_tmap_1(A_785, B_786, C_787, D_788)) | ~l1_struct_0(D_788) | ~m1_subset_1(C_787, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_785), u1_struct_0(B_786)))) | ~v1_funct_2(C_787, u1_struct_0(A_785), u1_struct_0(B_786)) | ~v1_funct_1(C_787) | ~l1_struct_0(B_786) | ~l1_struct_0(A_785))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_5029, plain, (![D_788]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_788)) | ~l1_struct_0(D_788) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_5027])).
% 8.91/2.91  tff(c_5032, plain, (![D_788]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_788)) | ~l1_struct_0(D_788) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_5029])).
% 8.91/2.91  tff(c_5033, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_5032])).
% 8.91/2.91  tff(c_5036, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_5033])).
% 8.91/2.91  tff(c_5040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_5036])).
% 8.91/2.91  tff(c_5041, plain, (![D_788]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_788)) | ~l1_struct_0(D_788))), inference(splitRight, [status(thm)], [c_5032])).
% 8.91/2.91  tff(c_5043, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_5041])).
% 8.91/2.91  tff(c_5046, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_5043])).
% 8.91/2.91  tff(c_5050, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_5046])).
% 8.91/2.91  tff(c_5053, plain, (![D_789]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_789)) | ~l1_struct_0(D_789))), inference(splitRight, [status(thm)], [c_5041])).
% 8.91/2.91  tff(c_82, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_3407, plain, (![A_473, B_474, C_475, D_476]: (v1_funct_1(k2_tmap_1(A_473, B_474, C_475, D_476)) | ~l1_struct_0(D_476) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_473), u1_struct_0(B_474)))) | ~v1_funct_2(C_475, u1_struct_0(A_473), u1_struct_0(B_474)) | ~v1_funct_1(C_475) | ~l1_struct_0(B_474) | ~l1_struct_0(A_473))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_3409, plain, (![D_476]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_476)) | ~l1_struct_0(D_476) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_3407])).
% 8.91/2.91  tff(c_3412, plain, (![D_476]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_476)) | ~l1_struct_0(D_476) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3409])).
% 8.91/2.91  tff(c_3413, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3412])).
% 8.91/2.91  tff(c_3416, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_3413])).
% 8.91/2.91  tff(c_3420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_3416])).
% 8.91/2.91  tff(c_3422, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3412])).
% 8.91/2.91  tff(c_3421, plain, (![D_476]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_476)) | ~l1_struct_0(D_476))), inference(splitRight, [status(thm)], [c_3412])).
% 8.91/2.91  tff(c_3423, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3421])).
% 8.91/2.91  tff(c_3426, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_3423])).
% 8.91/2.91  tff(c_3430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_3426])).
% 8.91/2.91  tff(c_3432, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3421])).
% 8.91/2.91  tff(c_3433, plain, (![A_477, B_478, C_479, D_480]: (v1_funct_2(k2_tmap_1(A_477, B_478, C_479, D_480), u1_struct_0(D_480), u1_struct_0(B_478)) | ~l1_struct_0(D_480) | ~m1_subset_1(C_479, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_477), u1_struct_0(B_478)))) | ~v1_funct_2(C_479, u1_struct_0(A_477), u1_struct_0(B_478)) | ~v1_funct_1(C_479) | ~l1_struct_0(B_478) | ~l1_struct_0(A_477))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_3435, plain, (![D_480]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_480), u1_struct_0(D_480), u1_struct_0('#skF_2')) | ~l1_struct_0(D_480) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_3433])).
% 8.91/2.91  tff(c_3440, plain, (![D_482]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_482), u1_struct_0(D_482), u1_struct_0('#skF_2')) | ~l1_struct_0(D_482))), inference(demodulation, [status(thm), theory('equality')], [c_3422, c_3432, c_70, c_68, c_3435])).
% 8.91/2.91  tff(c_3298, plain, (![A_442, B_443, C_444, D_445]: (v1_funct_1(k2_tmap_1(A_442, B_443, C_444, D_445)) | ~l1_struct_0(D_445) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_442), u1_struct_0(B_443)))) | ~v1_funct_2(C_444, u1_struct_0(A_442), u1_struct_0(B_443)) | ~v1_funct_1(C_444) | ~l1_struct_0(B_443) | ~l1_struct_0(A_442))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_3300, plain, (![D_445]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_445)) | ~l1_struct_0(D_445) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_3298])).
% 8.91/2.91  tff(c_3303, plain, (![D_445]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_445)) | ~l1_struct_0(D_445) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3300])).
% 8.91/2.91  tff(c_3304, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3303])).
% 8.91/2.91  tff(c_3313, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_3304])).
% 8.91/2.91  tff(c_3317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_3313])).
% 8.91/2.91  tff(c_3319, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3303])).
% 8.91/2.91  tff(c_3318, plain, (![D_445]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_445)) | ~l1_struct_0(D_445))), inference(splitRight, [status(thm)], [c_3303])).
% 8.91/2.91  tff(c_3320, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3318])).
% 8.91/2.91  tff(c_3323, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_3320])).
% 8.91/2.91  tff(c_3327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_3323])).
% 8.91/2.91  tff(c_3329, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3318])).
% 8.91/2.91  tff(c_3331, plain, (![A_451, B_452, C_453, D_454]: (v1_funct_2(k2_tmap_1(A_451, B_452, C_453, D_454), u1_struct_0(D_454), u1_struct_0(B_452)) | ~l1_struct_0(D_454) | ~m1_subset_1(C_453, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_451), u1_struct_0(B_452)))) | ~v1_funct_2(C_453, u1_struct_0(A_451), u1_struct_0(B_452)) | ~v1_funct_1(C_453) | ~l1_struct_0(B_452) | ~l1_struct_0(A_451))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_3333, plain, (![D_454]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_454), u1_struct_0(D_454), u1_struct_0('#skF_2')) | ~l1_struct_0(D_454) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_3331])).
% 8.91/2.91  tff(c_3337, plain, (![D_455]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_455), u1_struct_0(D_455), u1_struct_0('#skF_2')) | ~l1_struct_0(D_455))), inference(demodulation, [status(thm), theory('equality')], [c_3319, c_3329, c_70, c_68, c_3333])).
% 8.91/2.91  tff(c_3170, plain, (![A_411, B_412, C_413, D_414]: (v1_funct_1(k2_tmap_1(A_411, B_412, C_413, D_414)) | ~l1_struct_0(D_414) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_411), u1_struct_0(B_412)))) | ~v1_funct_2(C_413, u1_struct_0(A_411), u1_struct_0(B_412)) | ~v1_funct_1(C_413) | ~l1_struct_0(B_412) | ~l1_struct_0(A_411))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_3172, plain, (![D_414]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_414)) | ~l1_struct_0(D_414) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_3170])).
% 8.91/2.91  tff(c_3175, plain, (![D_414]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_414)) | ~l1_struct_0(D_414) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3172])).
% 8.91/2.91  tff(c_3176, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3175])).
% 8.91/2.91  tff(c_3179, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_3176])).
% 8.91/2.91  tff(c_3183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_3179])).
% 8.91/2.91  tff(c_3185, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3175])).
% 8.91/2.91  tff(c_3184, plain, (![D_414]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_414)) | ~l1_struct_0(D_414))), inference(splitRight, [status(thm)], [c_3175])).
% 8.91/2.91  tff(c_3186, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3184])).
% 8.91/2.91  tff(c_3189, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_3186])).
% 8.91/2.91  tff(c_3193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_3189])).
% 8.91/2.91  tff(c_3195, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3184])).
% 8.91/2.91  tff(c_3204, plain, (![A_421, B_422, C_423, D_424]: (m1_subset_1(k2_tmap_1(A_421, B_422, C_423, D_424), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_424), u1_struct_0(B_422)))) | ~l1_struct_0(D_424) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_421), u1_struct_0(B_422)))) | ~v1_funct_2(C_423, u1_struct_0(A_421), u1_struct_0(B_422)) | ~v1_funct_1(C_423) | ~l1_struct_0(B_422) | ~l1_struct_0(A_421))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_3020, plain, (![A_379, B_380, C_381, D_382]: (v1_funct_1(k2_tmap_1(A_379, B_380, C_381, D_382)) | ~l1_struct_0(D_382) | ~m1_subset_1(C_381, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_379), u1_struct_0(B_380)))) | ~v1_funct_2(C_381, u1_struct_0(A_379), u1_struct_0(B_380)) | ~v1_funct_1(C_381) | ~l1_struct_0(B_380) | ~l1_struct_0(A_379))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_3024, plain, (![D_382]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_382)) | ~l1_struct_0(D_382) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_3020])).
% 8.91/2.91  tff(c_3030, plain, (![D_382]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_382)) | ~l1_struct_0(D_382) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3024])).
% 8.91/2.91  tff(c_3031, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3030])).
% 8.91/2.91  tff(c_3034, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_3031])).
% 8.91/2.91  tff(c_3038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_3034])).
% 8.91/2.91  tff(c_3040, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_3030])).
% 8.91/2.91  tff(c_3039, plain, (![D_382]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_382)) | ~l1_struct_0(D_382))), inference(splitRight, [status(thm)], [c_3030])).
% 8.91/2.91  tff(c_3052, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3039])).
% 8.91/2.91  tff(c_3055, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_3052])).
% 8.91/2.91  tff(c_3059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_3055])).
% 8.91/2.91  tff(c_3061, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3039])).
% 8.91/2.91  tff(c_3079, plain, (![A_390, B_391, C_392, D_393]: (m1_subset_1(k2_tmap_1(A_390, B_391, C_392, D_393), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_393), u1_struct_0(B_391)))) | ~l1_struct_0(D_393) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_390), u1_struct_0(B_391)))) | ~v1_funct_2(C_392, u1_struct_0(A_390), u1_struct_0(B_391)) | ~v1_funct_1(C_392) | ~l1_struct_0(B_391) | ~l1_struct_0(A_390))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_168, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_248, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_168])).
% 8.91/2.91  tff(c_158, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_251, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_158])).
% 8.91/2.91  tff(c_148, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_250, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_148])).
% 8.91/2.91  tff(c_138, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_253, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_138])).
% 8.91/2.91  tff(c_128, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_237, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_128])).
% 8.91/2.91  tff(c_118, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_252, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_118])).
% 8.91/2.91  tff(c_108, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_249, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_108])).
% 8.91/2.91  tff(c_98, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_276, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_98])).
% 8.91/2.91  tff(c_84, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_182, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_84])).
% 8.91/2.91  tff(c_192, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_182])).
% 8.91/2.91  tff(c_202, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_192])).
% 8.91/2.91  tff(c_600, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_251, c_250, c_253, c_237, c_252, c_249, c_276, c_202])).
% 8.91/2.91  tff(c_54, plain, (r4_tsep_1('#skF_1', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_56, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_356, plain, (![A_123, B_124, C_125]: (m1_pre_topc(k1_tsep_1(A_123, B_124, C_125), A_123) | ~m1_pre_topc(C_125, A_123) | v2_struct_0(C_125) | ~m1_pre_topc(B_124, A_123) | v2_struct_0(B_124) | ~l1_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.91/2.91  tff(c_362, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_56, c_356])).
% 8.91/2.91  tff(c_365, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_62, c_58, c_362])).
% 8.91/2.91  tff(c_366, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_82, c_64, c_60, c_365])).
% 8.91/2.91  tff(c_80, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.91/2.91  tff(c_299, plain, (![A_110, B_111, C_112, D_113]: (k2_partfun1(A_110, B_111, C_112, D_113)=k7_relat_1(C_112, D_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(C_112))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.91/2.91  tff(c_305, plain, (![D_113]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_113)=k7_relat_1('#skF_3', D_113) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_299])).
% 8.91/2.91  tff(c_314, plain, (![D_113]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_113)=k7_relat_1('#skF_3', D_113))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_305])).
% 8.91/2.91  tff(c_511, plain, (![A_153, B_154, C_155, D_156]: (k2_partfun1(u1_struct_0(A_153), u1_struct_0(B_154), C_155, u1_struct_0(D_156))=k2_tmap_1(A_153, B_154, C_155, D_156) | ~m1_pre_topc(D_156, A_153) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_153), u1_struct_0(B_154)))) | ~v1_funct_2(C_155, u1_struct_0(A_153), u1_struct_0(B_154)) | ~v1_funct_1(C_155) | ~l1_pre_topc(B_154) | ~v2_pre_topc(B_154) | v2_struct_0(B_154) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.91/2.91  tff(c_519, plain, (![D_156]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_156))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_156) | ~m1_pre_topc(D_156, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_511])).
% 8.91/2.91  tff(c_531, plain, (![D_156]: (k7_relat_1('#skF_3', u1_struct_0(D_156))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_156) | ~m1_pre_topc(D_156, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_70, c_68, c_314, c_519])).
% 8.91/2.91  tff(c_533, plain, (![D_157]: (k7_relat_1('#skF_3', u1_struct_0(D_157))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_157) | ~m1_pre_topc(D_157, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_531])).
% 8.91/2.91  tff(c_4, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.91/2.91  tff(c_225, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_4])).
% 8.91/2.91  tff(c_232, plain, (![C_107, A_108, B_109]: (v4_relat_1(C_107, A_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.91/2.91  tff(c_236, plain, (v4_relat_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_232])).
% 8.91/2.91  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.91/2.91  tff(c_240, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_236, c_2])).
% 8.91/2.91  tff(c_243, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_225, c_240])).
% 8.91/2.91  tff(c_539, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_533, c_243])).
% 8.91/2.91  tff(c_548, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_366, c_539])).
% 8.91/2.91  tff(c_2355, plain, (![D_344, B_347, C_346, E_348, A_345]: (v5_pre_topc(k2_tmap_1(A_345, B_347, E_348, k1_tsep_1(A_345, C_346, D_344)), k1_tsep_1(A_345, C_346, D_344), B_347) | ~m1_subset_1(k2_tmap_1(A_345, B_347, E_348, D_344), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_344), u1_struct_0(B_347)))) | ~v5_pre_topc(k2_tmap_1(A_345, B_347, E_348, D_344), D_344, B_347) | ~v1_funct_2(k2_tmap_1(A_345, B_347, E_348, D_344), u1_struct_0(D_344), u1_struct_0(B_347)) | ~v1_funct_1(k2_tmap_1(A_345, B_347, E_348, D_344)) | ~m1_subset_1(k2_tmap_1(A_345, B_347, E_348, C_346), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346), u1_struct_0(B_347)))) | ~v5_pre_topc(k2_tmap_1(A_345, B_347, E_348, C_346), C_346, B_347) | ~v1_funct_2(k2_tmap_1(A_345, B_347, E_348, C_346), u1_struct_0(C_346), u1_struct_0(B_347)) | ~v1_funct_1(k2_tmap_1(A_345, B_347, E_348, C_346)) | ~m1_subset_1(E_348, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_345), u1_struct_0(B_347)))) | ~v1_funct_2(E_348, u1_struct_0(A_345), u1_struct_0(B_347)) | ~v1_funct_1(E_348) | ~r4_tsep_1(A_345, C_346, D_344) | ~m1_pre_topc(D_344, A_345) | v2_struct_0(D_344) | ~m1_pre_topc(C_346, A_345) | v2_struct_0(C_346) | ~l1_pre_topc(B_347) | ~v2_pre_topc(B_347) | v2_struct_0(B_347) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.91/2.91  tff(c_2365, plain, (![C_346]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_346, '#skF_5')), k1_tsep_1('#skF_1', C_346, '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346), C_346, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346), u1_struct_0(C_346), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~r4_tsep_1('#skF_1', C_346, '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_346, '#skF_1') | v2_struct_0(C_346) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_276, c_2355])).
% 8.91/2.91  tff(c_2380, plain, (![C_346]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_346, '#skF_5')), k1_tsep_1('#skF_1', C_346, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346), C_346, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346), u1_struct_0(C_346), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_346)) | ~r4_tsep_1('#skF_1', C_346, '#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(C_346, '#skF_1') | v2_struct_0(C_346) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_58, c_70, c_68, c_66, c_237, c_252, c_249, c_2365])).
% 8.91/2.91  tff(c_2922, plain, (![C_360]: (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', C_360, '#skF_5')), k1_tsep_1('#skF_1', C_360, '#skF_5'), '#skF_2') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), C_360, '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360), u1_struct_0(C_360), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', C_360)) | ~r4_tsep_1('#skF_1', C_360, '#skF_5') | ~m1_pre_topc(C_360, '#skF_1') | v2_struct_0(C_360))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_60, c_2380])).
% 8.91/2.91  tff(c_2935, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_2') | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_253, c_2922])).
% 8.91/2.91  tff(c_2948, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54, c_248, c_251, c_250, c_548, c_56, c_56, c_2935])).
% 8.91/2.91  tff(c_2950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_600, c_2948])).
% 8.91/2.91  tff(c_2952, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_98])).
% 8.91/2.91  tff(c_3088, plain, (~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3079, c_2952])).
% 8.91/2.91  tff(c_3103, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3040, c_3061, c_70, c_68, c_66, c_3088])).
% 8.91/2.91  tff(c_3109, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12, c_3103])).
% 8.91/2.91  tff(c_3113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_3109])).
% 8.91/2.91  tff(c_3115, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_138])).
% 8.91/2.91  tff(c_3213, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3204, c_3115])).
% 8.91/2.91  tff(c_3228, plain, (~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3185, c_3195, c_70, c_68, c_66, c_3213])).
% 8.91/2.91  tff(c_3234, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3228])).
% 8.91/2.91  tff(c_3238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_3234])).
% 8.91/2.91  tff(c_3240, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_118])).
% 8.91/2.91  tff(c_3341, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_3337, c_3240])).
% 8.91/2.91  tff(c_3344, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12, c_3341])).
% 8.91/2.91  tff(c_3348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_3344])).
% 8.91/2.91  tff(c_3350, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_158])).
% 8.91/2.91  tff(c_3444, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_3440, c_3350])).
% 8.91/2.91  tff(c_3447, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3444])).
% 8.91/2.91  tff(c_3451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_3447])).
% 8.91/2.91  tff(c_3453, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_148])).
% 8.91/2.91  tff(c_3489, plain, (![A_494, B_495, C_496]: (m1_pre_topc(k1_tsep_1(A_494, B_495, C_496), A_494) | ~m1_pre_topc(C_496, A_494) | v2_struct_0(C_496) | ~m1_pre_topc(B_495, A_494) | v2_struct_0(B_495) | ~l1_pre_topc(A_494) | v2_struct_0(A_494))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.91/2.91  tff(c_3495, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_56, c_3489])).
% 8.91/2.91  tff(c_3498, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_62, c_58, c_3495])).
% 8.91/2.91  tff(c_3499, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_82, c_64, c_60, c_3498])).
% 8.91/2.91  tff(c_3457, plain, (![A_483, B_484, C_485, D_486]: (k2_partfun1(A_483, B_484, C_485, D_486)=k7_relat_1(C_485, D_486) | ~m1_subset_1(C_485, k1_zfmisc_1(k2_zfmisc_1(A_483, B_484))) | ~v1_funct_1(C_485))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.91/2.91  tff(c_3459, plain, (![D_486]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_486)=k7_relat_1('#skF_3', D_486) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_3457])).
% 8.91/2.91  tff(c_3462, plain, (![D_486]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_486)=k7_relat_1('#skF_3', D_486))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3459])).
% 8.91/2.91  tff(c_3612, plain, (![A_530, B_531, C_532, D_533]: (k2_partfun1(u1_struct_0(A_530), u1_struct_0(B_531), C_532, u1_struct_0(D_533))=k2_tmap_1(A_530, B_531, C_532, D_533) | ~m1_pre_topc(D_533, A_530) | ~m1_subset_1(C_532, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_530), u1_struct_0(B_531)))) | ~v1_funct_2(C_532, u1_struct_0(A_530), u1_struct_0(B_531)) | ~v1_funct_1(C_532) | ~l1_pre_topc(B_531) | ~v2_pre_topc(B_531) | v2_struct_0(B_531) | ~l1_pre_topc(A_530) | ~v2_pre_topc(A_530) | v2_struct_0(A_530))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.91/2.91  tff(c_3616, plain, (![D_533]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_533))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_533) | ~m1_pre_topc(D_533, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_3612])).
% 8.91/2.91  tff(c_3620, plain, (![D_533]: (k7_relat_1('#skF_3', u1_struct_0(D_533))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_533) | ~m1_pre_topc(D_533, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_70, c_68, c_3462, c_3616])).
% 8.91/2.91  tff(c_3622, plain, (![D_534]: (k7_relat_1('#skF_3', u1_struct_0(D_534))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_534) | ~m1_pre_topc(D_534, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_3620])).
% 8.91/2.91  tff(c_3628, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3622, c_243])).
% 8.91/2.91  tff(c_3637, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3628])).
% 8.91/2.91  tff(c_3452, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_148])).
% 8.91/2.91  tff(c_3852, plain, (![C_582, A_581, B_583, D_580, E_584]: (v5_pre_topc(k2_tmap_1(A_581, B_583, E_584, C_582), C_582, B_583) | ~m1_subset_1(k2_tmap_1(A_581, B_583, E_584, k1_tsep_1(A_581, C_582, D_580)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_581, C_582, D_580)), u1_struct_0(B_583)))) | ~v5_pre_topc(k2_tmap_1(A_581, B_583, E_584, k1_tsep_1(A_581, C_582, D_580)), k1_tsep_1(A_581, C_582, D_580), B_583) | ~v1_funct_2(k2_tmap_1(A_581, B_583, E_584, k1_tsep_1(A_581, C_582, D_580)), u1_struct_0(k1_tsep_1(A_581, C_582, D_580)), u1_struct_0(B_583)) | ~v1_funct_1(k2_tmap_1(A_581, B_583, E_584, k1_tsep_1(A_581, C_582, D_580))) | ~m1_subset_1(E_584, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_581), u1_struct_0(B_583)))) | ~v1_funct_2(E_584, u1_struct_0(A_581), u1_struct_0(B_583)) | ~v1_funct_1(E_584) | ~r4_tsep_1(A_581, C_582, D_580) | ~m1_pre_topc(D_580, A_581) | v2_struct_0(D_580) | ~m1_pre_topc(C_582, A_581) | v2_struct_0(C_582) | ~l1_pre_topc(B_583) | ~v2_pre_topc(B_583) | v2_struct_0(B_583) | ~l1_pre_topc(A_581) | ~v2_pre_topc(A_581) | v2_struct_0(A_581))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.91/2.91  tff(c_3859, plain, (![B_583, E_584]: (v5_pre_topc(k2_tmap_1('#skF_1', B_583, E_584, '#skF_4'), '#skF_4', B_583) | ~m1_subset_1(k2_tmap_1('#skF_1', B_583, E_584, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_583)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_583, E_584, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_583) | ~v1_funct_2(k2_tmap_1('#skF_1', B_583, E_584, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_583)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_583, E_584, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_584, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_583)))) | ~v1_funct_2(E_584, u1_struct_0('#skF_1'), u1_struct_0(B_583)) | ~v1_funct_1(E_584) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_583) | ~v2_pre_topc(B_583) | v2_struct_0(B_583) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_3852])).
% 8.91/2.91  tff(c_3865, plain, (![B_583, E_584]: (v5_pre_topc(k2_tmap_1('#skF_1', B_583, E_584, '#skF_4'), '#skF_4', B_583) | ~m1_subset_1(k2_tmap_1('#skF_1', B_583, E_584, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_583)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_583, E_584, '#skF_1'), '#skF_1', B_583) | ~v1_funct_2(k2_tmap_1('#skF_1', B_583, E_584, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_583)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_583, E_584, '#skF_1')) | ~m1_subset_1(E_584, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_583)))) | ~v1_funct_2(E_584, u1_struct_0('#skF_1'), u1_struct_0(B_583)) | ~v1_funct_1(E_584) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_583) | ~v2_pre_topc(B_583) | v2_struct_0(B_583) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_62, c_58, c_54, c_56, c_56, c_56, c_56, c_56, c_56, c_3859])).
% 8.91/2.91  tff(c_4002, plain, (![B_610, E_611]: (v5_pre_topc(k2_tmap_1('#skF_1', B_610, E_611, '#skF_4'), '#skF_4', B_610) | ~m1_subset_1(k2_tmap_1('#skF_1', B_610, E_611, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_610)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_610, E_611, '#skF_1'), '#skF_1', B_610) | ~v1_funct_2(k2_tmap_1('#skF_1', B_610, E_611, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_610)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_610, E_611, '#skF_1')) | ~m1_subset_1(E_611, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_610)))) | ~v1_funct_2(E_611, u1_struct_0('#skF_1'), u1_struct_0(B_610)) | ~v1_funct_1(E_611) | ~l1_pre_topc(B_610) | ~v2_pre_topc(B_610) | v2_struct_0(B_610))), inference(negUnitSimplification, [status(thm)], [c_82, c_64, c_60, c_3865])).
% 8.91/2.91  tff(c_4005, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3637, c_4002])).
% 8.91/2.91  tff(c_4011, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_70, c_3637, c_68, c_3637, c_3452, c_3637, c_66, c_4005])).
% 8.91/2.91  tff(c_4013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_3453, c_4011])).
% 8.91/2.91  tff(c_4015, plain, (~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_108])).
% 8.91/2.91  tff(c_4074, plain, (![A_629, B_630, C_631, D_632]: (v1_funct_1(k2_tmap_1(A_629, B_630, C_631, D_632)) | ~l1_struct_0(D_632) | ~m1_subset_1(C_631, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_629), u1_struct_0(B_630)))) | ~v1_funct_2(C_631, u1_struct_0(A_629), u1_struct_0(B_630)) | ~v1_funct_1(C_631) | ~l1_struct_0(B_630) | ~l1_struct_0(A_629))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_4076, plain, (![D_632]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_632)) | ~l1_struct_0(D_632) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_4074])).
% 8.91/2.91  tff(c_4079, plain, (![D_632]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_632)) | ~l1_struct_0(D_632) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_4076])).
% 8.91/2.91  tff(c_4080, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_4079])).
% 8.91/2.91  tff(c_4089, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_4080])).
% 8.91/2.91  tff(c_4093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_4089])).
% 8.91/2.91  tff(c_4095, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_4079])).
% 8.91/2.91  tff(c_4050, plain, (![A_623, B_624, C_625]: (m1_pre_topc(k1_tsep_1(A_623, B_624, C_625), A_623) | ~m1_pre_topc(C_625, A_623) | v2_struct_0(C_625) | ~m1_pre_topc(B_624, A_623) | v2_struct_0(B_624) | ~l1_pre_topc(A_623) | v2_struct_0(A_623))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.91/2.91  tff(c_4056, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_56, c_4050])).
% 8.91/2.91  tff(c_4059, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_62, c_58, c_4056])).
% 8.91/2.91  tff(c_4060, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_82, c_64, c_60, c_4059])).
% 8.91/2.91  tff(c_4020, plain, (![A_612, B_613, C_614, D_615]: (k2_partfun1(A_612, B_613, C_614, D_615)=k7_relat_1(C_614, D_615) | ~m1_subset_1(C_614, k1_zfmisc_1(k2_zfmisc_1(A_612, B_613))) | ~v1_funct_1(C_614))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.91/2.91  tff(c_4022, plain, (![D_615]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_615)=k7_relat_1('#skF_3', D_615) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_4020])).
% 8.91/2.91  tff(c_4025, plain, (![D_615]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_615)=k7_relat_1('#skF_3', D_615))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4022])).
% 8.91/2.91  tff(c_4181, plain, (![A_663, B_664, C_665, D_666]: (k2_partfun1(u1_struct_0(A_663), u1_struct_0(B_664), C_665, u1_struct_0(D_666))=k2_tmap_1(A_663, B_664, C_665, D_666) | ~m1_pre_topc(D_666, A_663) | ~m1_subset_1(C_665, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_663), u1_struct_0(B_664)))) | ~v1_funct_2(C_665, u1_struct_0(A_663), u1_struct_0(B_664)) | ~v1_funct_1(C_665) | ~l1_pre_topc(B_664) | ~v2_pre_topc(B_664) | v2_struct_0(B_664) | ~l1_pre_topc(A_663) | ~v2_pre_topc(A_663) | v2_struct_0(A_663))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.91/2.91  tff(c_4185, plain, (![D_666]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_666))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_666) | ~m1_pre_topc(D_666, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_4181])).
% 8.91/2.91  tff(c_4189, plain, (![D_666]: (k7_relat_1('#skF_3', u1_struct_0(D_666))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_666) | ~m1_pre_topc(D_666, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_70, c_68, c_4025, c_4185])).
% 8.91/2.91  tff(c_4191, plain, (![D_667]: (k7_relat_1('#skF_3', u1_struct_0(D_667))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_667) | ~m1_pre_topc(D_667, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_4189])).
% 8.91/2.91  tff(c_4197, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4191, c_243])).
% 8.91/2.91  tff(c_4206, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4060, c_4197])).
% 8.91/2.91  tff(c_4014, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_108])).
% 8.91/2.91  tff(c_4094, plain, (![D_632]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_632)) | ~l1_struct_0(D_632))), inference(splitRight, [status(thm)], [c_4079])).
% 8.91/2.91  tff(c_4096, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_4094])).
% 8.91/2.91  tff(c_4101, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_4096])).
% 8.91/2.91  tff(c_4105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_4101])).
% 8.91/2.91  tff(c_4106, plain, (![D_632]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_632)) | ~l1_struct_0(D_632))), inference(splitRight, [status(thm)], [c_4094])).
% 8.91/2.91  tff(c_4107, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_4094])).
% 8.91/2.91  tff(c_4109, plain, (![A_638, B_639, C_640, D_641]: (v1_funct_2(k2_tmap_1(A_638, B_639, C_640, D_641), u1_struct_0(D_641), u1_struct_0(B_639)) | ~l1_struct_0(D_641) | ~m1_subset_1(C_640, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_638), u1_struct_0(B_639)))) | ~v1_funct_2(C_640, u1_struct_0(A_638), u1_struct_0(B_639)) | ~v1_funct_1(C_640) | ~l1_struct_0(B_639) | ~l1_struct_0(A_638))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_4111, plain, (![D_641]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641), u1_struct_0(D_641), u1_struct_0('#skF_2')) | ~l1_struct_0(D_641) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_4109])).
% 8.91/2.91  tff(c_4114, plain, (![D_641]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641), u1_struct_0(D_641), u1_struct_0('#skF_2')) | ~l1_struct_0(D_641))), inference(demodulation, [status(thm), theory('equality')], [c_4095, c_4107, c_70, c_68, c_4111])).
% 8.91/2.91  tff(c_24, plain, (![A_35, B_36, C_37, D_38]: (m1_subset_1(k2_tmap_1(A_35, B_36, C_37, D_38), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_38), u1_struct_0(B_36)))) | ~l1_struct_0(D_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35), u1_struct_0(B_36)))) | ~v1_funct_2(C_37, u1_struct_0(A_35), u1_struct_0(B_36)) | ~v1_funct_1(C_37) | ~l1_struct_0(B_36) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_4426, plain, (![D_720, A_719, B_723, D_722, C_721]: (k2_partfun1(u1_struct_0(D_722), u1_struct_0(B_723), k2_tmap_1(A_719, B_723, C_721, D_722), u1_struct_0(D_720))=k2_tmap_1(D_722, B_723, k2_tmap_1(A_719, B_723, C_721, D_722), D_720) | ~m1_pre_topc(D_720, D_722) | ~v1_funct_2(k2_tmap_1(A_719, B_723, C_721, D_722), u1_struct_0(D_722), u1_struct_0(B_723)) | ~v1_funct_1(k2_tmap_1(A_719, B_723, C_721, D_722)) | ~l1_pre_topc(B_723) | ~v2_pre_topc(B_723) | v2_struct_0(B_723) | ~l1_pre_topc(D_722) | ~v2_pre_topc(D_722) | v2_struct_0(D_722) | ~l1_struct_0(D_722) | ~m1_subset_1(C_721, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_719), u1_struct_0(B_723)))) | ~v1_funct_2(C_721, u1_struct_0(A_719), u1_struct_0(B_723)) | ~v1_funct_1(C_721) | ~l1_struct_0(B_723) | ~l1_struct_0(A_719))), inference(resolution, [status(thm)], [c_24, c_4181])).
% 8.91/2.91  tff(c_4430, plain, (![D_722, D_720]: (k2_partfun1(u1_struct_0(D_722), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_722), u1_struct_0(D_720))=k2_tmap_1(D_722, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_722), D_720) | ~m1_pre_topc(D_720, D_722) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_722), u1_struct_0(D_722), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_722)) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(D_722) | ~v2_pre_topc(D_722) | v2_struct_0(D_722) | ~l1_struct_0(D_722) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_4426])).
% 8.91/2.91  tff(c_4434, plain, (![D_722, D_720]: (k2_partfun1(u1_struct_0(D_722), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_722), u1_struct_0(D_720))=k2_tmap_1(D_722, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_722), D_720) | ~m1_pre_topc(D_720, D_722) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_722), u1_struct_0(D_722), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_722)) | v2_struct_0('#skF_2') | ~l1_pre_topc(D_722) | ~v2_pre_topc(D_722) | v2_struct_0(D_722) | ~l1_struct_0(D_722))), inference(demodulation, [status(thm), theory('equality')], [c_4095, c_4107, c_70, c_68, c_74, c_72, c_4430])).
% 8.91/2.91  tff(c_4454, plain, (![D_729, D_730]: (k2_partfun1(u1_struct_0(D_729), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_729), u1_struct_0(D_730))=k2_tmap_1(D_729, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_729), D_730) | ~m1_pre_topc(D_730, D_729) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_729), u1_struct_0(D_729), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_729)) | ~l1_pre_topc(D_729) | ~v2_pre_topc(D_729) | v2_struct_0(D_729) | ~l1_struct_0(D_729))), inference(negUnitSimplification, [status(thm)], [c_76, c_4434])).
% 8.91/2.91  tff(c_4116, plain, (![A_643, B_644, C_645, D_646]: (m1_subset_1(k2_tmap_1(A_643, B_644, C_645, D_646), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_646), u1_struct_0(B_644)))) | ~l1_struct_0(D_646) | ~m1_subset_1(C_645, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_643), u1_struct_0(B_644)))) | ~v1_funct_2(C_645, u1_struct_0(A_643), u1_struct_0(B_644)) | ~v1_funct_1(C_645) | ~l1_struct_0(B_644) | ~l1_struct_0(A_643))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.91/2.91  tff(c_10, plain, (![A_9, B_10, C_11, D_12]: (k2_partfun1(A_9, B_10, C_11, D_12)=k7_relat_1(C_11, D_12) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_1(C_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.91/2.91  tff(c_4252, plain, (![D_670, D_671, C_672, B_669, A_668]: (k2_partfun1(u1_struct_0(D_670), u1_struct_0(B_669), k2_tmap_1(A_668, B_669, C_672, D_670), D_671)=k7_relat_1(k2_tmap_1(A_668, B_669, C_672, D_670), D_671) | ~v1_funct_1(k2_tmap_1(A_668, B_669, C_672, D_670)) | ~l1_struct_0(D_670) | ~m1_subset_1(C_672, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_668), u1_struct_0(B_669)))) | ~v1_funct_2(C_672, u1_struct_0(A_668), u1_struct_0(B_669)) | ~v1_funct_1(C_672) | ~l1_struct_0(B_669) | ~l1_struct_0(A_668))), inference(resolution, [status(thm)], [c_4116, c_10])).
% 8.91/2.91  tff(c_4256, plain, (![D_670, D_671]: (k2_partfun1(u1_struct_0(D_670), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_670), D_671)=k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_670), D_671) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_670)) | ~l1_struct_0(D_670) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_4252])).
% 8.91/2.91  tff(c_4260, plain, (![D_670, D_671]: (k2_partfun1(u1_struct_0(D_670), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_670), D_671)=k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_670), D_671) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_670)) | ~l1_struct_0(D_670))), inference(demodulation, [status(thm), theory('equality')], [c_4095, c_4107, c_70, c_68, c_4256])).
% 8.91/2.91  tff(c_4476, plain, (![D_731, D_732]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_731), u1_struct_0(D_732))=k2_tmap_1(D_731, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_731), D_732) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_731)) | ~l1_struct_0(D_731) | ~m1_pre_topc(D_732, D_731) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_731), u1_struct_0(D_731), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_731)) | ~l1_pre_topc(D_731) | ~v2_pre_topc(D_731) | v2_struct_0(D_731) | ~l1_struct_0(D_731))), inference(superposition, [status(thm), theory('equality')], [c_4454, c_4260])).
% 8.91/2.91  tff(c_4485, plain, (![D_733, D_734]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_733), u1_struct_0(D_734))=k2_tmap_1(D_733, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_733), D_734) | ~m1_pre_topc(D_734, D_733) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_733)) | ~l1_pre_topc(D_733) | ~v2_pre_topc(D_733) | v2_struct_0(D_733) | ~l1_struct_0(D_733))), inference(resolution, [status(thm)], [c_4114, c_4476])).
% 8.91/2.91  tff(c_4138, plain, (![A_647, B_648, C_649, D_650]: (v1_relat_1(k2_tmap_1(A_647, B_648, C_649, D_650)) | ~l1_struct_0(D_650) | ~m1_subset_1(C_649, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_647), u1_struct_0(B_648)))) | ~v1_funct_2(C_649, u1_struct_0(A_647), u1_struct_0(B_648)) | ~v1_funct_1(C_649) | ~l1_struct_0(B_648) | ~l1_struct_0(A_647))), inference(resolution, [status(thm)], [c_4116, c_4])).
% 8.91/2.91  tff(c_4291, plain, (![B_686, D_684, A_682, C_683, D_685]: (v1_relat_1(k2_tmap_1(D_685, B_686, k2_tmap_1(A_682, B_686, C_683, D_685), D_684)) | ~l1_struct_0(D_684) | ~v1_funct_2(k2_tmap_1(A_682, B_686, C_683, D_685), u1_struct_0(D_685), u1_struct_0(B_686)) | ~v1_funct_1(k2_tmap_1(A_682, B_686, C_683, D_685)) | ~l1_struct_0(D_685) | ~m1_subset_1(C_683, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_682), u1_struct_0(B_686)))) | ~v1_funct_2(C_683, u1_struct_0(A_682), u1_struct_0(B_686)) | ~v1_funct_1(C_683) | ~l1_struct_0(B_686) | ~l1_struct_0(A_682))), inference(resolution, [status(thm)], [c_24, c_4138])).
% 8.91/2.91  tff(c_4295, plain, (![D_641, D_684]: (v1_relat_1(k2_tmap_1(D_641, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641), D_684)) | ~l1_struct_0(D_684) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | ~l1_struct_0(D_641))), inference(resolution, [status(thm)], [c_4114, c_4291])).
% 8.91/2.91  tff(c_4300, plain, (![D_641, D_684]: (v1_relat_1(k2_tmap_1(D_641, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641), D_684)) | ~l1_struct_0(D_684) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641)) | ~l1_struct_0(D_641))), inference(demodulation, [status(thm), theory('equality')], [c_4095, c_4107, c_70, c_68, c_66, c_4295])).
% 8.91/2.91  tff(c_4589, plain, (![D_737, D_738]: (v1_relat_1(k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_737), u1_struct_0(D_738))) | ~l1_struct_0(D_738) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_737)) | ~l1_struct_0(D_737) | ~m1_pre_topc(D_738, D_737) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_737)) | ~l1_pre_topc(D_737) | ~v2_pre_topc(D_737) | v2_struct_0(D_737) | ~l1_struct_0(D_737))), inference(superposition, [status(thm), theory('equality')], [c_4485, c_4300])).
% 8.91/2.91  tff(c_4595, plain, (![D_738]: (v1_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_738))) | ~l1_struct_0(D_738) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~l1_struct_0('#skF_1') | ~m1_pre_topc(D_738, '#skF_1') | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4206, c_4589])).
% 8.91/2.91  tff(c_4600, plain, (![D_738]: (v1_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_738))) | ~l1_struct_0(D_738) | ~m1_pre_topc(D_738, '#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4095, c_80, c_78, c_70, c_4206, c_4095, c_70, c_4206, c_4595])).
% 8.91/2.91  tff(c_4601, plain, (![D_738]: (v1_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_738))) | ~l1_struct_0(D_738) | ~m1_pre_topc(D_738, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_82, c_4600])).
% 8.91/2.91  tff(c_4190, plain, (![D_666]: (k7_relat_1('#skF_3', u1_struct_0(D_666))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_666) | ~m1_pre_topc(D_666, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_4189])).
% 8.91/2.91  tff(c_8, plain, (![C_8, A_6, B_7]: (v4_relat_1(C_8, A_6) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.91/2.91  tff(c_4148, plain, (![A_652, B_653, C_654, D_655]: (v4_relat_1(k2_tmap_1(A_652, B_653, C_654, D_655), u1_struct_0(D_655)) | ~l1_struct_0(D_655) | ~m1_subset_1(C_654, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_652), u1_struct_0(B_653)))) | ~v1_funct_2(C_654, u1_struct_0(A_652), u1_struct_0(B_653)) | ~v1_funct_1(C_654) | ~l1_struct_0(B_653) | ~l1_struct_0(A_652))), inference(resolution, [status(thm)], [c_4116, c_8])).
% 8.91/2.91  tff(c_4341, plain, (![A_701, C_703, B_705, D_704, D_702]: (v4_relat_1(k2_tmap_1(D_704, B_705, k2_tmap_1(A_701, B_705, C_703, D_704), D_702), u1_struct_0(D_702)) | ~l1_struct_0(D_702) | ~v1_funct_2(k2_tmap_1(A_701, B_705, C_703, D_704), u1_struct_0(D_704), u1_struct_0(B_705)) | ~v1_funct_1(k2_tmap_1(A_701, B_705, C_703, D_704)) | ~l1_struct_0(D_704) | ~m1_subset_1(C_703, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_701), u1_struct_0(B_705)))) | ~v1_funct_2(C_703, u1_struct_0(A_701), u1_struct_0(B_705)) | ~v1_funct_1(C_703) | ~l1_struct_0(B_705) | ~l1_struct_0(A_701))), inference(resolution, [status(thm)], [c_24, c_4148])).
% 8.91/2.91  tff(c_4345, plain, (![D_641, D_702]: (v4_relat_1(k2_tmap_1(D_641, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641), D_702), u1_struct_0(D_702)) | ~l1_struct_0(D_702) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | ~l1_struct_0(D_641))), inference(resolution, [status(thm)], [c_4114, c_4341])).
% 8.91/2.91  tff(c_4350, plain, (![D_641, D_702]: (v4_relat_1(k2_tmap_1(D_641, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641), D_702), u1_struct_0(D_702)) | ~l1_struct_0(D_702) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641)) | ~l1_struct_0(D_641))), inference(demodulation, [status(thm), theory('equality')], [c_4095, c_4107, c_70, c_68, c_66, c_4345])).
% 8.91/2.91  tff(c_4680, plain, (![D_751, D_752]: (v4_relat_1(k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_751), u1_struct_0(D_752)), u1_struct_0(D_752)) | ~l1_struct_0(D_752) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_751)) | ~l1_struct_0(D_751) | ~m1_pre_topc(D_752, D_751) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_751)) | ~l1_pre_topc(D_751) | ~v2_pre_topc(D_751) | v2_struct_0(D_751) | ~l1_struct_0(D_751))), inference(superposition, [status(thm), theory('equality')], [c_4485, c_4350])).
% 8.91/2.91  tff(c_4689, plain, (![D_752]: (v4_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_752)), u1_struct_0(D_752)) | ~l1_struct_0(D_752) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~l1_struct_0('#skF_1') | ~m1_pre_topc(D_752, '#skF_1') | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4206, c_4680])).
% 8.91/2.91  tff(c_4695, plain, (![D_752]: (v4_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_752)), u1_struct_0(D_752)) | ~l1_struct_0(D_752) | ~m1_pre_topc(D_752, '#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4095, c_80, c_78, c_70, c_4206, c_4095, c_70, c_4206, c_4689])).
% 8.91/2.91  tff(c_4697, plain, (![D_753]: (v4_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_753)), u1_struct_0(D_753)) | ~l1_struct_0(D_753) | ~m1_pre_topc(D_753, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_82, c_4695])).
% 8.91/2.91  tff(c_4710, plain, (![D_754]: (k7_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_754)), u1_struct_0(D_754))=k7_relat_1('#skF_3', u1_struct_0(D_754)) | ~v1_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_754))) | ~l1_struct_0(D_754) | ~m1_pre_topc(D_754, '#skF_1'))), inference(resolution, [status(thm)], [c_4697, c_2])).
% 8.91/2.91  tff(c_4727, plain, (![D_755]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_755), u1_struct_0(D_755))=k7_relat_1('#skF_3', u1_struct_0(D_755)) | ~v1_relat_1(k7_relat_1('#skF_3', u1_struct_0(D_755))) | ~l1_struct_0(D_755) | ~m1_pre_topc(D_755, '#skF_1') | ~m1_pre_topc(D_755, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4190, c_4710])).
% 8.91/2.91  tff(c_4737, plain, (![D_756]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_756), u1_struct_0(D_756))=k7_relat_1('#skF_3', u1_struct_0(D_756)) | ~l1_struct_0(D_756) | ~m1_pre_topc(D_756, '#skF_1'))), inference(resolution, [status(thm)], [c_4601, c_4727])).
% 8.91/2.91  tff(c_4484, plain, (![D_641, D_732]: (k7_relat_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641), u1_struct_0(D_732))=k2_tmap_1(D_641, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641), D_732) | ~m1_pre_topc(D_732, D_641) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_641)) | ~l1_pre_topc(D_641) | ~v2_pre_topc(D_641) | v2_struct_0(D_641) | ~l1_struct_0(D_641))), inference(resolution, [status(thm)], [c_4114, c_4476])).
% 8.91/2.91  tff(c_4776, plain, (![D_757]: (k2_tmap_1(D_757, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_757), D_757)=k7_relat_1('#skF_3', u1_struct_0(D_757)) | ~m1_pre_topc(D_757, D_757) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_757)) | ~l1_pre_topc(D_757) | ~v2_pre_topc(D_757) | v2_struct_0(D_757) | ~l1_struct_0(D_757) | ~l1_struct_0(D_757) | ~m1_pre_topc(D_757, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4737, c_4484])).
% 8.91/2.91  tff(c_4788, plain, (![D_632]: (k2_tmap_1(D_632, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_632), D_632)=k7_relat_1('#skF_3', u1_struct_0(D_632)) | ~m1_pre_topc(D_632, D_632) | ~l1_pre_topc(D_632) | ~v2_pre_topc(D_632) | v2_struct_0(D_632) | ~m1_pre_topc(D_632, '#skF_1') | ~l1_struct_0(D_632))), inference(resolution, [status(thm)], [c_4106, c_4776])).
% 8.91/2.91  tff(c_4646, plain, (![E_749, D_745, A_746, C_747, B_748]: (v5_pre_topc(k2_tmap_1(A_746, B_748, E_749, D_745), D_745, B_748) | ~m1_subset_1(k2_tmap_1(A_746, B_748, E_749, k1_tsep_1(A_746, C_747, D_745)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_746, C_747, D_745)), u1_struct_0(B_748)))) | ~v5_pre_topc(k2_tmap_1(A_746, B_748, E_749, k1_tsep_1(A_746, C_747, D_745)), k1_tsep_1(A_746, C_747, D_745), B_748) | ~v1_funct_2(k2_tmap_1(A_746, B_748, E_749, k1_tsep_1(A_746, C_747, D_745)), u1_struct_0(k1_tsep_1(A_746, C_747, D_745)), u1_struct_0(B_748)) | ~v1_funct_1(k2_tmap_1(A_746, B_748, E_749, k1_tsep_1(A_746, C_747, D_745))) | ~m1_subset_1(E_749, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_746), u1_struct_0(B_748)))) | ~v1_funct_2(E_749, u1_struct_0(A_746), u1_struct_0(B_748)) | ~v1_funct_1(E_749) | ~r4_tsep_1(A_746, C_747, D_745) | ~m1_pre_topc(D_745, A_746) | v2_struct_0(D_745) | ~m1_pre_topc(C_747, A_746) | v2_struct_0(C_747) | ~l1_pre_topc(B_748) | ~v2_pre_topc(B_748) | v2_struct_0(B_748) | ~l1_pre_topc(A_746) | ~v2_pre_topc(A_746) | v2_struct_0(A_746))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.91/2.91  tff(c_4660, plain, (![B_748, E_749]: (v5_pre_topc(k2_tmap_1('#skF_1', B_748, E_749, '#skF_5'), '#skF_5', B_748) | ~m1_subset_1(k2_tmap_1('#skF_1', B_748, E_749, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_748)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_748, E_749, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_748) | ~v1_funct_2(k2_tmap_1('#skF_1', B_748, E_749, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_748)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_748, E_749, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_749, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_748)))) | ~v1_funct_2(E_749, u1_struct_0('#skF_1'), u1_struct_0(B_748)) | ~v1_funct_1(E_749) | ~r4_tsep_1('#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_748) | ~v2_pre_topc(B_748) | v2_struct_0(B_748) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_4646])).
% 8.91/2.91  tff(c_4669, plain, (![B_748, E_749]: (v5_pre_topc(k2_tmap_1('#skF_1', B_748, E_749, '#skF_5'), '#skF_5', B_748) | ~m1_subset_1(k2_tmap_1('#skF_1', B_748, E_749, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_748)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_748, E_749, '#skF_1'), '#skF_1', B_748) | ~v1_funct_2(k2_tmap_1('#skF_1', B_748, E_749, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_748)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_748, E_749, '#skF_1')) | ~m1_subset_1(E_749, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_748)))) | ~v1_funct_2(E_749, u1_struct_0('#skF_1'), u1_struct_0(B_748)) | ~v1_funct_1(E_749) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_748) | ~v2_pre_topc(B_748) | v2_struct_0(B_748) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_62, c_58, c_54, c_56, c_56, c_56, c_56, c_56, c_56, c_4660])).
% 8.91/2.91  tff(c_4957, plain, (![B_769, E_770]: (v5_pre_topc(k2_tmap_1('#skF_1', B_769, E_770, '#skF_5'), '#skF_5', B_769) | ~m1_subset_1(k2_tmap_1('#skF_1', B_769, E_770, '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_769)))) | ~v5_pre_topc(k2_tmap_1('#skF_1', B_769, E_770, '#skF_1'), '#skF_1', B_769) | ~v1_funct_2(k2_tmap_1('#skF_1', B_769, E_770, '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0(B_769)) | ~v1_funct_1(k2_tmap_1('#skF_1', B_769, E_770, '#skF_1')) | ~m1_subset_1(E_770, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_769)))) | ~v1_funct_2(E_770, u1_struct_0('#skF_1'), u1_struct_0(B_769)) | ~v1_funct_1(E_770) | ~l1_pre_topc(B_769) | ~v2_pre_topc(B_769) | v2_struct_0(B_769))), inference(negUnitSimplification, [status(thm)], [c_82, c_64, c_60, c_4669])).
% 8.91/2.91  tff(c_4961, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_5'), '#skF_5', '#skF_2') | ~m1_subset_1(k7_relat_1('#skF_3', u1_struct_0('#skF_1')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1'), '#skF_1', '#skF_2') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), '#skF_1')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4788, c_4957])).
% 8.91/2.91  tff(c_4970, plain, (v5_pre_topc(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_5', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4095, c_4060, c_80, c_78, c_4060, c_74, c_72, c_70, c_4206, c_68, c_4206, c_66, c_4206, c_70, c_4206, c_4206, c_68, c_4206, c_4206, c_4014, c_4206, c_4206, c_66, c_243, c_4206, c_4961])).
% 8.91/2.91  tff(c_4972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_4015, c_4970])).
% 8.91/2.91  tff(c_4974, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_168])).
% 8.91/2.91  tff(c_5057, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_5053, c_4974])).
% 8.91/2.91  tff(c_5060, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_5057])).
% 8.91/2.91  tff(c_5064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_5060])).
% 8.91/2.91  tff(c_5066, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_128])).
% 8.91/2.91  tff(c_5175, plain, (~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5171, c_5066])).
% 8.91/2.91  tff(c_5178, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12, c_5175])).
% 8.91/2.91  tff(c_5182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_5178])).
% 8.91/2.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.91/2.91  
% 8.91/2.91  Inference rules
% 8.91/2.91  ----------------------
% 8.91/2.91  #Ref     : 0
% 8.91/2.91  #Sup     : 919
% 8.91/2.91  #Fact    : 0
% 8.91/2.91  #Define  : 0
% 8.91/2.91  #Split   : 40
% 8.91/2.91  #Chain   : 0
% 8.91/2.91  #Close   : 0
% 8.91/2.91  
% 8.91/2.91  Ordering : KBO
% 8.91/2.91  
% 8.91/2.91  Simplification rules
% 8.91/2.91  ----------------------
% 8.91/2.91  #Subsume      : 274
% 8.91/2.91  #Demod        : 3257
% 8.91/2.91  #Tautology    : 291
% 8.91/2.91  #SimpNegUnit  : 276
% 8.91/2.91  #BackRed      : 0
% 8.91/2.91  
% 8.91/2.91  #Partial instantiations: 0
% 8.91/2.91  #Strategies tried      : 1
% 8.91/2.91  
% 8.91/2.91  Timing (in seconds)
% 8.91/2.91  ----------------------
% 8.91/2.91  Preprocessing        : 0.45
% 8.91/2.91  Parsing              : 0.22
% 8.91/2.91  CNF conversion       : 0.05
% 8.91/2.91  Main loop            : 1.55
% 8.91/2.91  Inferencing          : 0.57
% 8.91/2.91  Reduction            : 0.55
% 8.91/2.91  Demodulation         : 0.43
% 8.91/2.91  BG Simplification    : 0.06
% 8.91/2.91  Subsumption          : 0.30
% 8.91/2.91  Abstraction          : 0.07
% 8.91/2.91  MUC search           : 0.00
% 8.91/2.91  Cooper               : 0.00
% 8.91/2.91  Total                : 2.10
% 8.91/2.91  Index Insertion      : 0.00
% 8.91/2.91  Index Deletion       : 0.00
% 8.91/2.91  Index Matching       : 0.00
% 8.91/2.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
