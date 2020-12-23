%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:18 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :  268 (3541 expanded)
%              Number of leaves         :   45 (1313 expanded)
%              Depth                    :   22
%              Number of atoms          :  829 (31862 expanded)
%              Number of equality atoms :   57 (1858 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_286,negated_conjecture,(
    ~ ! [A] :
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
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,u1_struct_0(D),u1_struct_0(B))
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                               => ( ( D = A
                                    & r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(D),u1_struct_0(B),E,G) )
                                 => ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,G),F)
                                  <=> r2_funct_2(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,E,C),F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).

tff(f_63,axiom,(
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

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_149,axiom,(
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

tff(f_179,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_131,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_217,axiom,(
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
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_1187,plain,(
    ! [A_406,B_407,D_408] :
      ( r2_funct_2(A_406,B_407,D_408,D_408)
      | ~ m1_subset_1(D_408,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407)))
      | ~ v1_funct_2(D_408,A_406,B_407)
      | ~ v1_funct_1(D_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1193,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_1187])).

tff(c_1202,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1193])).

tff(c_46,plain,(
    '#skF_1' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_80,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_95,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_80])).

tff(c_70,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_96,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_70])).

tff(c_108,plain,(
    ! [B_211,A_212] :
      ( l1_pre_topc(B_211)
      | ~ m1_pre_topc(B_211,A_212)
      | ~ l1_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_114,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_108])).

tff(c_120,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_114])).

tff(c_16,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1203,plain,(
    ! [A_409,B_410,C_411,D_412] :
      ( v1_funct_1(k2_tmap_1(A_409,B_410,C_411,D_412))
      | ~ l1_struct_0(D_412)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_409),u1_struct_0(B_410))))
      | ~ v1_funct_2(C_411,u1_struct_0(A_409),u1_struct_0(B_410))
      | ~ v1_funct_1(C_411)
      | ~ l1_struct_0(B_410)
      | ~ l1_struct_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1209,plain,(
    ! [D_412] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_412))
      | ~ l1_struct_0(D_412)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_1203])).

tff(c_1218,plain,(
    ! [D_412] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_412))
      | ~ l1_struct_0(D_412)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1209])).

tff(c_1219,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1218])).

tff(c_1222,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1219])).

tff(c_1226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_1222])).

tff(c_1228,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1218])).

tff(c_52,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_50,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_1207,plain,(
    ! [D_412] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_412))
      | ~ l1_struct_0(D_412)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_1203])).

tff(c_1215,plain,(
    ! [D_412] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_412))
      | ~ l1_struct_0(D_412)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1207])).

tff(c_1229,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1215])).

tff(c_1232,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_1229])).

tff(c_1236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1232])).

tff(c_1238,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1215])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_1227,plain,(
    ! [D_412] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_412))
      | ~ l1_struct_0(D_412) ) ),
    inference(splitRight,[status(thm)],[c_1218])).

tff(c_1239,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1227])).

tff(c_1266,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1239])).

tff(c_1270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1266])).

tff(c_1272,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1227])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_62,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_99,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_62])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_100,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_60])).

tff(c_1320,plain,(
    ! [A_426,B_427,C_428,D_429] :
      ( v1_funct_2(k2_tmap_1(A_426,B_427,C_428,D_429),u1_struct_0(D_429),u1_struct_0(B_427))
      | ~ l1_struct_0(D_429)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_426),u1_struct_0(B_427))))
      | ~ v1_funct_2(C_428,u1_struct_0(A_426),u1_struct_0(B_427))
      | ~ v1_funct_1(C_428)
      | ~ l1_struct_0(B_427)
      | ~ l1_struct_0(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1322,plain,(
    ! [D_429] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_429),u1_struct_0(D_429),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_429)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_1320])).

tff(c_1329,plain,(
    ! [D_429] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_429),u1_struct_0(D_429),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_429) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_1272,c_64,c_99,c_1322])).

tff(c_28,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( m1_subset_1(k2_tmap_1(A_43,B_44,C_45,D_46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_46),u1_struct_0(B_44))))
      | ~ l1_struct_0(D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),u1_struct_0(B_44))))
      | ~ v1_funct_2(C_45,u1_struct_0(A_43),u1_struct_0(B_44))
      | ~ v1_funct_1(C_45)
      | ~ l1_struct_0(B_44)
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1205,plain,(
    ! [D_412] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_412))
      | ~ l1_struct_0(D_412)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_1203])).

tff(c_1212,plain,(
    ! [D_412] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_412))
      | ~ l1_struct_0(D_412)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_1205])).

tff(c_1278,plain,(
    ! [D_412] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_412))
      | ~ l1_struct_0(D_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_1272,c_1212])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_82,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_94,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_82])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_98,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_66])).

tff(c_1829,plain,(
    ! [E_528,B_530,D_529,A_527,C_531] :
      ( m1_subset_1(k3_tmap_1(A_527,B_530,C_531,D_529,E_528),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_529),u1_struct_0(B_530))))
      | ~ m1_subset_1(E_528,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_531),u1_struct_0(B_530))))
      | ~ v1_funct_2(E_528,u1_struct_0(C_531),u1_struct_0(B_530))
      | ~ v1_funct_1(E_528)
      | ~ m1_pre_topc(D_529,A_527)
      | ~ m1_pre_topc(C_531,A_527)
      | ~ l1_pre_topc(B_530)
      | ~ v2_pre_topc(B_530)
      | v2_struct_0(B_530)
      | ~ l1_pre_topc(A_527)
      | ~ v2_pre_topc(A_527)
      | v2_struct_0(A_527) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1687,plain,(
    ! [B_500,E_498,A_497,C_501,D_499] :
      ( v1_funct_2(k3_tmap_1(A_497,B_500,C_501,D_499,E_498),u1_struct_0(D_499),u1_struct_0(B_500))
      | ~ m1_subset_1(E_498,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_501),u1_struct_0(B_500))))
      | ~ v1_funct_2(E_498,u1_struct_0(C_501),u1_struct_0(B_500))
      | ~ v1_funct_1(E_498)
      | ~ m1_pre_topc(D_499,A_497)
      | ~ m1_pre_topc(C_501,A_497)
      | ~ l1_pre_topc(B_500)
      | ~ v2_pre_topc(B_500)
      | v2_struct_0(B_500)
      | ~ l1_pre_topc(A_497)
      | ~ v2_pre_topc(A_497)
      | v2_struct_0(A_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1691,plain,(
    ! [A_497,D_499] :
      ( v1_funct_2(k3_tmap_1(A_497,'#skF_2','#skF_4',D_499,'#skF_5'),u1_struct_0(D_499),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_499,A_497)
      | ~ m1_pre_topc('#skF_4',A_497)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_497)
      | ~ v2_pre_topc(A_497)
      | v2_struct_0(A_497) ) ),
    inference(resolution,[status(thm)],[c_100,c_1687])).

tff(c_1697,plain,(
    ! [A_497,D_499] :
      ( v1_funct_2(k3_tmap_1(A_497,'#skF_2','#skF_4',D_499,'#skF_5'),u1_struct_0(D_499),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_499,A_497)
      | ~ m1_pre_topc('#skF_4',A_497)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_497)
      | ~ v2_pre_topc(A_497)
      | v2_struct_0(A_497) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_99,c_1691])).

tff(c_1703,plain,(
    ! [A_502,D_503] :
      ( v1_funct_2(k3_tmap_1(A_502,'#skF_2','#skF_4',D_503,'#skF_5'),u1_struct_0(D_503),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_503,A_502)
      | ~ m1_pre_topc('#skF_4',A_502)
      | ~ l1_pre_topc(A_502)
      | ~ v2_pre_topc(A_502)
      | v2_struct_0(A_502) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1697])).

tff(c_1563,plain,(
    ! [A_476,B_479,D_478,E_477,C_480] :
      ( v1_funct_1(k3_tmap_1(A_476,B_479,C_480,D_478,E_477))
      | ~ m1_subset_1(E_477,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_480),u1_struct_0(B_479))))
      | ~ v1_funct_2(E_477,u1_struct_0(C_480),u1_struct_0(B_479))
      | ~ v1_funct_1(E_477)
      | ~ m1_pre_topc(D_478,A_476)
      | ~ m1_pre_topc(C_480,A_476)
      | ~ l1_pre_topc(B_479)
      | ~ v2_pre_topc(B_479)
      | v2_struct_0(B_479)
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1567,plain,(
    ! [A_476,D_478] :
      ( v1_funct_1(k3_tmap_1(A_476,'#skF_2','#skF_4',D_478,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_478,A_476)
      | ~ m1_pre_topc('#skF_4',A_476)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(resolution,[status(thm)],[c_100,c_1563])).

tff(c_1573,plain,(
    ! [A_476,D_478] :
      ( v1_funct_1(k3_tmap_1(A_476,'#skF_2','#skF_4',D_478,'#skF_5'))
      | ~ m1_pre_topc(D_478,A_476)
      | ~ m1_pre_topc('#skF_4',A_476)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_99,c_1567])).

tff(c_1579,plain,(
    ! [A_481,D_482] :
      ( v1_funct_1(k3_tmap_1(A_481,'#skF_2','#skF_4',D_482,'#skF_5'))
      | ~ m1_pre_topc(D_482,A_481)
      | ~ m1_pre_topc('#skF_4',A_481)
      | ~ l1_pre_topc(A_481)
      | ~ v2_pre_topc(A_481)
      | v2_struct_0(A_481) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1573])).

tff(c_1337,plain,(
    ! [C_432,B_435,D_434,A_431,F_433] :
      ( r1_funct_2(A_431,B_435,C_432,D_434,F_433,F_433)
      | ~ m1_subset_1(F_433,k1_zfmisc_1(k2_zfmisc_1(C_432,D_434)))
      | ~ v1_funct_2(F_433,C_432,D_434)
      | ~ m1_subset_1(F_433,k1_zfmisc_1(k2_zfmisc_1(A_431,B_435)))
      | ~ v1_funct_2(F_433,A_431,B_435)
      | ~ v1_funct_1(F_433)
      | v1_xboole_0(D_434)
      | v1_xboole_0(B_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1339,plain,(
    ! [A_431,B_435] :
      ( r1_funct_2(A_431,B_435,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_431,B_435)))
      | ~ v1_funct_2('#skF_5',A_431,B_435)
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_435) ) ),
    inference(resolution,[status(thm)],[c_100,c_1337])).

tff(c_1346,plain,(
    ! [A_431,B_435] :
      ( r1_funct_2(A_431,B_435,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_431,B_435)))
      | ~ v1_funct_2('#skF_5',A_431,B_435)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_1339])).

tff(c_1355,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1346])).

tff(c_20,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1359,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1355,c_20])).

tff(c_1362,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1272,c_1359])).

tff(c_1364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1362])).

tff(c_1366,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1346])).

tff(c_44,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_102,plain,(
    r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_1463,plain,(
    ! [E_468,C_467,D_470,A_466,B_471,F_469] :
      ( F_469 = E_468
      | ~ r1_funct_2(A_466,B_471,C_467,D_470,E_468,F_469)
      | ~ m1_subset_1(F_469,k1_zfmisc_1(k2_zfmisc_1(C_467,D_470)))
      | ~ v1_funct_2(F_469,C_467,D_470)
      | ~ v1_funct_1(F_469)
      | ~ m1_subset_1(E_468,k1_zfmisc_1(k2_zfmisc_1(A_466,B_471)))
      | ~ v1_funct_2(E_468,A_466,B_471)
      | ~ v1_funct_1(E_468)
      | v1_xboole_0(D_470)
      | v1_xboole_0(B_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1471,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_102,c_1463])).

tff(c_1489,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_100,c_52,c_50,c_48,c_1471])).

tff(c_1490,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1366,c_1489])).

tff(c_285,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( v1_funct_1(k2_tmap_1(A_241,B_242,C_243,D_244))
      | ~ l1_struct_0(D_244)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_241),u1_struct_0(B_242))))
      | ~ v1_funct_2(C_243,u1_struct_0(A_241),u1_struct_0(B_242))
      | ~ v1_funct_1(C_243)
      | ~ l1_struct_0(B_242)
      | ~ l1_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_287,plain,(
    ! [D_244] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_244))
      | ~ l1_struct_0(D_244)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_285])).

tff(c_294,plain,(
    ! [D_244] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_244))
      | ~ l1_struct_0(D_244)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_287])).

tff(c_325,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_328,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_325])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_328])).

tff(c_334,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_289,plain,(
    ! [D_244] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_244))
      | ~ l1_struct_0(D_244)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_285])).

tff(c_297,plain,(
    ! [D_244] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_244))
      | ~ l1_struct_0(D_244)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_289])).

tff(c_336,plain,(
    ! [D_244] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_244))
      | ~ l1_struct_0(D_244)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_297])).

tff(c_337,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_340,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_337])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_340])).

tff(c_346,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_594,plain,(
    ! [F_290,B_292,A_288,C_289,D_291] :
      ( r1_funct_2(A_288,B_292,C_289,D_291,F_290,F_290)
      | ~ m1_subset_1(F_290,k1_zfmisc_1(k2_zfmisc_1(C_289,D_291)))
      | ~ v1_funct_2(F_290,C_289,D_291)
      | ~ m1_subset_1(F_290,k1_zfmisc_1(k2_zfmisc_1(A_288,B_292)))
      | ~ v1_funct_2(F_290,A_288,B_292)
      | ~ v1_funct_1(F_290)
      | v1_xboole_0(D_291)
      | v1_xboole_0(B_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_598,plain,(
    ! [A_288,B_292] :
      ( r1_funct_2(A_288,B_292,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_7','#skF_7')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_288,B_292)))
      | ~ v1_funct_2('#skF_7',A_288,B_292)
      | ~ v1_funct_1('#skF_7')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_292) ) ),
    inference(resolution,[status(thm)],[c_48,c_594])).

tff(c_606,plain,(
    ! [A_288,B_292] :
      ( r1_funct_2(A_288,B_292,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_7','#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_288,B_292)))
      | ~ v1_funct_2('#skF_7',A_288,B_292)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_598])).

tff(c_618,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_606])).

tff(c_621,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_618,c_20])).

tff(c_624,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_621])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_624])).

tff(c_628,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_606])).

tff(c_740,plain,(
    ! [D_328,B_329,F_327,E_326,C_325,A_324] :
      ( F_327 = E_326
      | ~ r1_funct_2(A_324,B_329,C_325,D_328,E_326,F_327)
      | ~ m1_subset_1(F_327,k1_zfmisc_1(k2_zfmisc_1(C_325,D_328)))
      | ~ v1_funct_2(F_327,C_325,D_328)
      | ~ v1_funct_1(F_327)
      | ~ m1_subset_1(E_326,k1_zfmisc_1(k2_zfmisc_1(A_324,B_329)))
      | ~ v1_funct_2(E_326,A_324,B_329)
      | ~ v1_funct_1(E_326)
      | v1_xboole_0(D_328)
      | v1_xboole_0(B_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_748,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_102,c_740])).

tff(c_766,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_100,c_52,c_50,c_48,c_748])).

tff(c_767,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_628,c_766])).

tff(c_86,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_101,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_86])).

tff(c_188,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_775,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_188])).

tff(c_291,plain,(
    ! [D_244] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_244))
      | ~ l1_struct_0(D_244)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_285])).

tff(c_300,plain,(
    ! [D_244] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_244))
      | ~ l1_struct_0(D_244)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_291])).

tff(c_352,plain,(
    ! [D_244] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_244))
      | ~ l1_struct_0(D_244)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_300])).

tff(c_353,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_372,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_353])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_372])).

tff(c_378,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_520,plain,(
    ! [A_279,B_280,C_281,D_282] :
      ( v1_funct_2(k2_tmap_1(A_279,B_280,C_281,D_282),u1_struct_0(D_282),u1_struct_0(B_280))
      | ~ l1_struct_0(D_282)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_279),u1_struct_0(B_280))))
      | ~ v1_funct_2(C_281,u1_struct_0(A_279),u1_struct_0(B_280))
      | ~ v1_funct_1(C_281)
      | ~ l1_struct_0(B_280)
      | ~ l1_struct_0(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_524,plain,(
    ! [D_282] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_282),u1_struct_0(D_282),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_282)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_520])).

tff(c_541,plain,(
    ! [D_283] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_283),u1_struct_0(D_283),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_346,c_64,c_99,c_524])).

tff(c_442,plain,(
    ! [A_274,B_275,C_276,D_277] :
      ( m1_subset_1(k2_tmap_1(A_274,B_275,C_276,D_277),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_277),u1_struct_0(B_275))))
      | ~ l1_struct_0(D_277)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_274),u1_struct_0(B_275))))
      | ~ v1_funct_2(C_276,u1_struct_0(A_274),u1_struct_0(B_275))
      | ~ v1_funct_1(C_276)
      | ~ l1_struct_0(B_275)
      | ~ l1_struct_0(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_333,plain,(
    ! [D_244] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_244))
      | ~ l1_struct_0(D_244) ) ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_349,plain,(
    ! [D_244] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_244))
      | ~ l1_struct_0(D_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_333])).

tff(c_92,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_97,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_92])).

tff(c_241,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_97])).

tff(c_301,plain,(
    ! [D_245,C_246,A_247,B_248] :
      ( D_245 = C_246
      | ~ r2_funct_2(A_247,B_248,C_246,D_245)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248)))
      | ~ v1_funct_2(D_245,A_247,B_248)
      | ~ v1_funct_1(D_245)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248)))
      | ~ v1_funct_2(C_246,A_247,B_248)
      | ~ v1_funct_1(C_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_303,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_241,c_301])).

tff(c_312,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_303])).

tff(c_380,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_383,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_349,c_380])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_383])).

tff(c_388,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_390,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_449,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_442,c_390])).

tff(c_470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_346,c_64,c_99,c_100,c_378,c_449])).

tff(c_471,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_506,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_544,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_541,c_506])).

tff(c_548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_544])).

tff(c_549,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_209,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( k2_partfun1(A_229,B_230,C_231,D_232) = k7_relat_1(C_231,D_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ v1_funct_1(C_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_211,plain,(
    ! [D_232] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_232) = k7_relat_1('#skF_5',D_232)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_209])).

tff(c_218,plain,(
    ! [D_232] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_232) = k7_relat_1('#skF_5',D_232) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_211])).

tff(c_859,plain,(
    ! [A_339,B_340,C_341,D_342] :
      ( k2_partfun1(u1_struct_0(A_339),u1_struct_0(B_340),C_341,u1_struct_0(D_342)) = k2_tmap_1(A_339,B_340,C_341,D_342)
      | ~ m1_pre_topc(D_342,A_339)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_339),u1_struct_0(B_340))))
      | ~ v1_funct_2(C_341,u1_struct_0(A_339),u1_struct_0(B_340))
      | ~ v1_funct_1(C_341)
      | ~ l1_pre_topc(B_340)
      | ~ v2_pre_topc(B_340)
      | v2_struct_0(B_340)
      | ~ l1_pre_topc(A_339)
      | ~ v2_pre_topc(A_339)
      | v2_struct_0(A_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_863,plain,(
    ! [D_342] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_342)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_342)
      | ~ m1_pre_topc(D_342,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_859])).

tff(c_869,plain,(
    ! [D_342] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_342)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_342)
      | ~ m1_pre_topc(D_342,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_76,c_74,c_64,c_99,c_218,c_863])).

tff(c_875,plain,(
    ! [D_343] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_343)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_343)
      | ~ m1_pre_topc(D_343,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_78,c_869])).

tff(c_122,plain,(
    ! [C_214,A_215,B_216] :
      ( v1_relat_1(C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_122])).

tff(c_149,plain,(
    ! [C_222,A_223,B_224] :
      ( v4_relat_1(C_222,A_223)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    v4_relat_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_100,c_149])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_164,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_159,c_2])).

tff(c_167,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_164])).

tff(c_881,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_875,c_167])).

tff(c_890,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_881])).

tff(c_1067,plain,(
    ! [D_387,A_389,C_390,B_388,E_391] :
      ( r2_funct_2(u1_struct_0(C_390),u1_struct_0(B_388),k3_tmap_1(A_389,B_388,D_387,C_390,k2_tmap_1(A_389,B_388,E_391,D_387)),k2_tmap_1(A_389,B_388,E_391,C_390))
      | ~ m1_pre_topc(C_390,D_387)
      | ~ m1_subset_1(E_391,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_389),u1_struct_0(B_388))))
      | ~ v1_funct_2(E_391,u1_struct_0(A_389),u1_struct_0(B_388))
      | ~ v1_funct_1(E_391)
      | ~ m1_pre_topc(D_387,A_389)
      | v2_struct_0(D_387)
      | ~ m1_pre_topc(C_390,A_389)
      | v2_struct_0(C_390)
      | ~ l1_pre_topc(B_388)
      | ~ v2_pre_topc(B_388)
      | v2_struct_0(B_388)
      | ~ l1_pre_topc(A_389)
      | ~ v2_pre_topc(A_389)
      | v2_struct_0(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_1072,plain,(
    ! [C_390] :
      ( r2_funct_2(u1_struct_0(C_390),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_390,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_390))
      | ~ m1_pre_topc(C_390,'#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_390,'#skF_4')
      | v2_struct_0(C_390)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_1067])).

tff(c_1084,plain,(
    ! [C_390] :
      ( r2_funct_2(u1_struct_0(C_390),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_390,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_390))
      | ~ m1_pre_topc(C_390,'#skF_4')
      | v2_struct_0(C_390)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_76,c_74,c_98,c_64,c_99,c_100,c_1072])).

tff(c_1100,plain,(
    ! [C_394] :
      ( r2_funct_2(u1_struct_0(C_394),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_394,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_394))
      | ~ m1_pre_topc(C_394,'#skF_4')
      | v2_struct_0(C_394) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_78,c_1084])).

tff(c_1108,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_1100])).

tff(c_1114,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1108])).

tff(c_1116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_775,c_1114])).

tff(c_1118,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_1296,plain,(
    ! [D_422,C_423,A_424,B_425] :
      ( D_422 = C_423
      | ~ r2_funct_2(A_424,B_425,C_423,D_422)
      | ~ m1_subset_1(D_422,k1_zfmisc_1(k2_zfmisc_1(A_424,B_425)))
      | ~ v1_funct_2(D_422,A_424,B_425)
      | ~ v1_funct_1(D_422)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_424,B_425)))
      | ~ v1_funct_2(C_423,A_424,B_425)
      | ~ v1_funct_1(C_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1304,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1118,c_1296])).

tff(c_1319,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7') = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1304])).

tff(c_1561,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1490,c_1490,c_1490,c_1319])).

tff(c_1562,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1561])).

tff(c_1582,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1579,c_1562])).

tff(c_1585,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_98,c_96,c_1582])).

tff(c_1587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1585])).

tff(c_1589,plain,(
    v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1561])).

tff(c_1498,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1118])).

tff(c_14,plain,(
    ! [D_16,C_15,A_13,B_14] :
      ( D_16 = C_15
      | ~ r2_funct_2(A_13,B_14,C_15,D_16)
      | ~ m1_subset_1(D_16,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(D_16,A_13,B_14)
      | ~ v1_funct_1(D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1539,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1498,c_14])).

tff(c_1542,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1539])).

tff(c_1591,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1542])).

tff(c_1592,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1591])).

tff(c_1706,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1703,c_1592])).

tff(c_1709,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_98,c_96,c_1706])).

tff(c_1711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1709])).

tff(c_1712,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1591])).

tff(c_1714,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1712])).

tff(c_1836,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1829,c_1714])).

tff(c_1868,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_76,c_74,c_98,c_96,c_64,c_99,c_100,c_1836])).

tff(c_1870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_78,c_1868])).

tff(c_1871,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1712])).

tff(c_1144,plain,(
    ! [A_399,B_400,C_401,D_402] :
      ( k2_partfun1(A_399,B_400,C_401,D_402) = k7_relat_1(C_401,D_402)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_399,B_400)))
      | ~ v1_funct_1(C_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1146,plain,(
    ! [D_402] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_402) = k7_relat_1('#skF_5',D_402)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_1144])).

tff(c_1153,plain,(
    ! [D_402] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_402) = k7_relat_1('#skF_5',D_402) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1146])).

tff(c_1909,plain,(
    ! [A_539,B_540,C_541,D_542] :
      ( k2_partfun1(u1_struct_0(A_539),u1_struct_0(B_540),C_541,u1_struct_0(D_542)) = k2_tmap_1(A_539,B_540,C_541,D_542)
      | ~ m1_pre_topc(D_542,A_539)
      | ~ m1_subset_1(C_541,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_539),u1_struct_0(B_540))))
      | ~ v1_funct_2(C_541,u1_struct_0(A_539),u1_struct_0(B_540))
      | ~ v1_funct_1(C_541)
      | ~ l1_pre_topc(B_540)
      | ~ v2_pre_topc(B_540)
      | v2_struct_0(B_540)
      | ~ l1_pre_topc(A_539)
      | ~ v2_pre_topc(A_539)
      | v2_struct_0(A_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1913,plain,(
    ! [D_542] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_542)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_542)
      | ~ m1_pre_topc(D_542,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_1909])).

tff(c_1919,plain,(
    ! [D_542] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_542)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_542)
      | ~ m1_pre_topc(D_542,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_76,c_74,c_64,c_99,c_1153,c_1913])).

tff(c_1925,plain,(
    ! [D_543] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_543)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_543)
      | ~ m1_pre_topc(D_543,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_78,c_1919])).

tff(c_1931,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1925,c_167])).

tff(c_1940,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1931])).

tff(c_2089,plain,(
    ! [C_572,D_569,A_571,B_570,E_573] :
      ( r2_funct_2(u1_struct_0(C_572),u1_struct_0(B_570),k3_tmap_1(A_571,B_570,D_569,C_572,k2_tmap_1(A_571,B_570,E_573,D_569)),k2_tmap_1(A_571,B_570,E_573,C_572))
      | ~ m1_pre_topc(C_572,D_569)
      | ~ m1_subset_1(E_573,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_571),u1_struct_0(B_570))))
      | ~ v1_funct_2(E_573,u1_struct_0(A_571),u1_struct_0(B_570))
      | ~ v1_funct_1(E_573)
      | ~ m1_pre_topc(D_569,A_571)
      | v2_struct_0(D_569)
      | ~ m1_pre_topc(C_572,A_571)
      | v2_struct_0(C_572)
      | ~ l1_pre_topc(B_570)
      | ~ v2_pre_topc(B_570)
      | v2_struct_0(B_570)
      | ~ l1_pre_topc(A_571)
      | ~ v2_pre_topc(A_571)
      | v2_struct_0(A_571) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_2094,plain,(
    ! [C_572] :
      ( r2_funct_2(u1_struct_0(C_572),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_572,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_572))
      | ~ m1_pre_topc(C_572,'#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_572,'#skF_4')
      | v2_struct_0(C_572)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1940,c_2089])).

tff(c_2100,plain,(
    ! [C_572] :
      ( r2_funct_2(u1_struct_0(C_572),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_572,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_572))
      | ~ m1_pre_topc(C_572,'#skF_4')
      | v2_struct_0(C_572)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_76,c_74,c_98,c_64,c_99,c_100,c_2094])).

tff(c_2105,plain,(
    ! [C_574] :
      ( r2_funct_2(u1_struct_0(C_574),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_574,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_574))
      | ~ m1_pre_topc(C_574,'#skF_4')
      | v2_struct_0(C_574) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_78,c_2100])).

tff(c_2113,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1871,c_2105])).

tff(c_2119,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2113])).

tff(c_2120,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2119])).

tff(c_2122,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2120,c_14])).

tff(c_2125,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2122])).

tff(c_2143,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2125])).

tff(c_2165,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1278,c_2143])).

tff(c_2169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_2165])).

tff(c_2170,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2125])).

tff(c_2172,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2170])).

tff(c_2190,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_2172])).

tff(c_2194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_1272,c_64,c_99,c_100,c_1228,c_2190])).

tff(c_2195,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2170])).

tff(c_2321,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2195])).

tff(c_2324,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1329,c_2321])).

tff(c_2328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_2324])).

tff(c_2329,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2195])).

tff(c_1117,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_2345,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2329,c_1117])).

tff(c_2355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_2345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.60/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.68/2.08  
% 5.68/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.68/2.08  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.68/2.08  
% 5.68/2.08  %Foreground sorts:
% 5.68/2.08  
% 5.68/2.08  
% 5.68/2.08  %Background operators:
% 5.68/2.08  
% 5.68/2.08  
% 5.68/2.08  %Foreground operators:
% 5.68/2.08  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.68/2.08  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.68/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.68/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.68/2.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.68/2.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.68/2.08  tff('#skF_7', type, '#skF_7': $i).
% 5.68/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.68/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.68/2.08  tff('#skF_6', type, '#skF_6': $i).
% 5.68/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.68/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.68/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.68/2.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.68/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.68/2.08  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.68/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.68/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.68/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.68/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.68/2.08  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 5.68/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.68/2.08  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.68/2.08  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.68/2.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.68/2.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.68/2.08  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.68/2.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.68/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.68/2.08  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.68/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.68/2.08  
% 5.91/2.14  tff(f_286, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tmap_1)).
% 5.91/2.14  tff(f_63, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 5.91/2.14  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.91/2.14  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.91/2.14  tff(f_149, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 5.91/2.14  tff(f_179, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 5.91/2.14  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 5.91/2.14  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.91/2.14  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.91/2.14  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.91/2.14  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.91/2.14  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.91/2.14  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.91/2.14  tff(f_217, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tmap_1)).
% 5.91/2.14  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_56, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_1187, plain, (![A_406, B_407, D_408]: (r2_funct_2(A_406, B_407, D_408, D_408) | ~m1_subset_1(D_408, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))) | ~v1_funct_2(D_408, A_406, B_407) | ~v1_funct_1(D_408))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.91/2.14  tff(c_1193, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_1187])).
% 5.91/2.14  tff(c_1202, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1193])).
% 5.91/2.14  tff(c_46, plain, ('#skF_1'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_80, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_95, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_80])).
% 5.91/2.14  tff(c_70, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_96, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_70])).
% 5.91/2.14  tff(c_108, plain, (![B_211, A_212]: (l1_pre_topc(B_211) | ~m1_pre_topc(B_211, A_212) | ~l1_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.91/2.14  tff(c_114, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_108])).
% 5.91/2.14  tff(c_120, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_114])).
% 5.91/2.14  tff(c_16, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.91/2.14  tff(c_1203, plain, (![A_409, B_410, C_411, D_412]: (v1_funct_1(k2_tmap_1(A_409, B_410, C_411, D_412)) | ~l1_struct_0(D_412) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_409), u1_struct_0(B_410)))) | ~v1_funct_2(C_411, u1_struct_0(A_409), u1_struct_0(B_410)) | ~v1_funct_1(C_411) | ~l1_struct_0(B_410) | ~l1_struct_0(A_409))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.91/2.14  tff(c_1209, plain, (![D_412]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_412)) | ~l1_struct_0(D_412) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_1203])).
% 5.91/2.14  tff(c_1218, plain, (![D_412]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_412)) | ~l1_struct_0(D_412) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1209])).
% 5.91/2.14  tff(c_1219, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1218])).
% 5.91/2.14  tff(c_1222, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_1219])).
% 5.91/2.14  tff(c_1226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_1222])).
% 5.91/2.14  tff(c_1228, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1218])).
% 5.91/2.14  tff(c_52, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_50, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_1207, plain, (![D_412]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_412)) | ~l1_struct_0(D_412) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_1203])).
% 5.91/2.14  tff(c_1215, plain, (![D_412]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_412)) | ~l1_struct_0(D_412) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1207])).
% 5.91/2.14  tff(c_1229, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1215])).
% 5.91/2.14  tff(c_1232, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_1229])).
% 5.91/2.14  tff(c_1236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_1232])).
% 5.91/2.14  tff(c_1238, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1215])).
% 5.91/2.14  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_1227, plain, (![D_412]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_412)) | ~l1_struct_0(D_412))), inference(splitRight, [status(thm)], [c_1218])).
% 5.91/2.14  tff(c_1239, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1227])).
% 5.91/2.14  tff(c_1266, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1239])).
% 5.91/2.14  tff(c_1270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1266])).
% 5.91/2.14  tff(c_1272, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1227])).
% 5.91/2.14  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_62, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_99, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_62])).
% 5.91/2.14  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_100, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_60])).
% 5.91/2.14  tff(c_1320, plain, (![A_426, B_427, C_428, D_429]: (v1_funct_2(k2_tmap_1(A_426, B_427, C_428, D_429), u1_struct_0(D_429), u1_struct_0(B_427)) | ~l1_struct_0(D_429) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_426), u1_struct_0(B_427)))) | ~v1_funct_2(C_428, u1_struct_0(A_426), u1_struct_0(B_427)) | ~v1_funct_1(C_428) | ~l1_struct_0(B_427) | ~l1_struct_0(A_426))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.91/2.14  tff(c_1322, plain, (![D_429]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_429), u1_struct_0(D_429), u1_struct_0('#skF_2')) | ~l1_struct_0(D_429) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_1320])).
% 5.91/2.14  tff(c_1329, plain, (![D_429]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_429), u1_struct_0(D_429), u1_struct_0('#skF_2')) | ~l1_struct_0(D_429))), inference(demodulation, [status(thm), theory('equality')], [c_1238, c_1272, c_64, c_99, c_1322])).
% 5.91/2.14  tff(c_28, plain, (![A_43, B_44, C_45, D_46]: (m1_subset_1(k2_tmap_1(A_43, B_44, C_45, D_46), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_46), u1_struct_0(B_44)))) | ~l1_struct_0(D_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), u1_struct_0(B_44)))) | ~v1_funct_2(C_45, u1_struct_0(A_43), u1_struct_0(B_44)) | ~v1_funct_1(C_45) | ~l1_struct_0(B_44) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.91/2.14  tff(c_1205, plain, (![D_412]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_412)) | ~l1_struct_0(D_412) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_1203])).
% 5.91/2.14  tff(c_1212, plain, (![D_412]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_412)) | ~l1_struct_0(D_412) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_1205])).
% 5.91/2.14  tff(c_1278, plain, (![D_412]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_412)) | ~l1_struct_0(D_412))), inference(demodulation, [status(thm), theory('equality')], [c_1238, c_1272, c_1212])).
% 5.91/2.14  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_82, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_94, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_82])).
% 5.91/2.14  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_66, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_98, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_66])).
% 5.91/2.14  tff(c_1829, plain, (![E_528, B_530, D_529, A_527, C_531]: (m1_subset_1(k3_tmap_1(A_527, B_530, C_531, D_529, E_528), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_529), u1_struct_0(B_530)))) | ~m1_subset_1(E_528, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_531), u1_struct_0(B_530)))) | ~v1_funct_2(E_528, u1_struct_0(C_531), u1_struct_0(B_530)) | ~v1_funct_1(E_528) | ~m1_pre_topc(D_529, A_527) | ~m1_pre_topc(C_531, A_527) | ~l1_pre_topc(B_530) | ~v2_pre_topc(B_530) | v2_struct_0(B_530) | ~l1_pre_topc(A_527) | ~v2_pre_topc(A_527) | v2_struct_0(A_527))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.91/2.14  tff(c_1687, plain, (![B_500, E_498, A_497, C_501, D_499]: (v1_funct_2(k3_tmap_1(A_497, B_500, C_501, D_499, E_498), u1_struct_0(D_499), u1_struct_0(B_500)) | ~m1_subset_1(E_498, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_501), u1_struct_0(B_500)))) | ~v1_funct_2(E_498, u1_struct_0(C_501), u1_struct_0(B_500)) | ~v1_funct_1(E_498) | ~m1_pre_topc(D_499, A_497) | ~m1_pre_topc(C_501, A_497) | ~l1_pre_topc(B_500) | ~v2_pre_topc(B_500) | v2_struct_0(B_500) | ~l1_pre_topc(A_497) | ~v2_pre_topc(A_497) | v2_struct_0(A_497))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.91/2.14  tff(c_1691, plain, (![A_497, D_499]: (v1_funct_2(k3_tmap_1(A_497, '#skF_2', '#skF_4', D_499, '#skF_5'), u1_struct_0(D_499), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_499, A_497) | ~m1_pre_topc('#skF_4', A_497) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_497) | ~v2_pre_topc(A_497) | v2_struct_0(A_497))), inference(resolution, [status(thm)], [c_100, c_1687])).
% 5.91/2.14  tff(c_1697, plain, (![A_497, D_499]: (v1_funct_2(k3_tmap_1(A_497, '#skF_2', '#skF_4', D_499, '#skF_5'), u1_struct_0(D_499), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_499, A_497) | ~m1_pre_topc('#skF_4', A_497) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_497) | ~v2_pre_topc(A_497) | v2_struct_0(A_497))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_99, c_1691])).
% 5.91/2.14  tff(c_1703, plain, (![A_502, D_503]: (v1_funct_2(k3_tmap_1(A_502, '#skF_2', '#skF_4', D_503, '#skF_5'), u1_struct_0(D_503), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_503, A_502) | ~m1_pre_topc('#skF_4', A_502) | ~l1_pre_topc(A_502) | ~v2_pre_topc(A_502) | v2_struct_0(A_502))), inference(negUnitSimplification, [status(thm)], [c_78, c_1697])).
% 5.91/2.14  tff(c_1563, plain, (![A_476, B_479, D_478, E_477, C_480]: (v1_funct_1(k3_tmap_1(A_476, B_479, C_480, D_478, E_477)) | ~m1_subset_1(E_477, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_480), u1_struct_0(B_479)))) | ~v1_funct_2(E_477, u1_struct_0(C_480), u1_struct_0(B_479)) | ~v1_funct_1(E_477) | ~m1_pre_topc(D_478, A_476) | ~m1_pre_topc(C_480, A_476) | ~l1_pre_topc(B_479) | ~v2_pre_topc(B_479) | v2_struct_0(B_479) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.91/2.14  tff(c_1567, plain, (![A_476, D_478]: (v1_funct_1(k3_tmap_1(A_476, '#skF_2', '#skF_4', D_478, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_478, A_476) | ~m1_pre_topc('#skF_4', A_476) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(resolution, [status(thm)], [c_100, c_1563])).
% 5.91/2.14  tff(c_1573, plain, (![A_476, D_478]: (v1_funct_1(k3_tmap_1(A_476, '#skF_2', '#skF_4', D_478, '#skF_5')) | ~m1_pre_topc(D_478, A_476) | ~m1_pre_topc('#skF_4', A_476) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_99, c_1567])).
% 5.91/2.14  tff(c_1579, plain, (![A_481, D_482]: (v1_funct_1(k3_tmap_1(A_481, '#skF_2', '#skF_4', D_482, '#skF_5')) | ~m1_pre_topc(D_482, A_481) | ~m1_pre_topc('#skF_4', A_481) | ~l1_pre_topc(A_481) | ~v2_pre_topc(A_481) | v2_struct_0(A_481))), inference(negUnitSimplification, [status(thm)], [c_78, c_1573])).
% 5.91/2.14  tff(c_1337, plain, (![C_432, B_435, D_434, A_431, F_433]: (r1_funct_2(A_431, B_435, C_432, D_434, F_433, F_433) | ~m1_subset_1(F_433, k1_zfmisc_1(k2_zfmisc_1(C_432, D_434))) | ~v1_funct_2(F_433, C_432, D_434) | ~m1_subset_1(F_433, k1_zfmisc_1(k2_zfmisc_1(A_431, B_435))) | ~v1_funct_2(F_433, A_431, B_435) | ~v1_funct_1(F_433) | v1_xboole_0(D_434) | v1_xboole_0(B_435))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.91/2.14  tff(c_1339, plain, (![A_431, B_435]: (r1_funct_2(A_431, B_435, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_431, B_435))) | ~v1_funct_2('#skF_5', A_431, B_435) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_435))), inference(resolution, [status(thm)], [c_100, c_1337])).
% 5.91/2.14  tff(c_1346, plain, (![A_431, B_435]: (r1_funct_2(A_431, B_435, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_431, B_435))) | ~v1_funct_2('#skF_5', A_431, B_435) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_435))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_1339])).
% 5.91/2.14  tff(c_1355, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1346])).
% 5.91/2.14  tff(c_20, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.91/2.14  tff(c_1359, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1355, c_20])).
% 5.91/2.14  tff(c_1362, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1272, c_1359])).
% 5.91/2.14  tff(c_1364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1362])).
% 5.91/2.14  tff(c_1366, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1346])).
% 5.91/2.14  tff(c_44, plain, (r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_102, plain, (r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 5.91/2.14  tff(c_1463, plain, (![E_468, C_467, D_470, A_466, B_471, F_469]: (F_469=E_468 | ~r1_funct_2(A_466, B_471, C_467, D_470, E_468, F_469) | ~m1_subset_1(F_469, k1_zfmisc_1(k2_zfmisc_1(C_467, D_470))) | ~v1_funct_2(F_469, C_467, D_470) | ~v1_funct_1(F_469) | ~m1_subset_1(E_468, k1_zfmisc_1(k2_zfmisc_1(A_466, B_471))) | ~v1_funct_2(E_468, A_466, B_471) | ~v1_funct_1(E_468) | v1_xboole_0(D_470) | v1_xboole_0(B_471))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.91/2.14  tff(c_1471, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_102, c_1463])).
% 5.91/2.14  tff(c_1489, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_100, c_52, c_50, c_48, c_1471])).
% 5.91/2.14  tff(c_1490, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1366, c_1489])).
% 5.91/2.14  tff(c_285, plain, (![A_241, B_242, C_243, D_244]: (v1_funct_1(k2_tmap_1(A_241, B_242, C_243, D_244)) | ~l1_struct_0(D_244) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_241), u1_struct_0(B_242)))) | ~v1_funct_2(C_243, u1_struct_0(A_241), u1_struct_0(B_242)) | ~v1_funct_1(C_243) | ~l1_struct_0(B_242) | ~l1_struct_0(A_241))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.91/2.14  tff(c_287, plain, (![D_244]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_244)) | ~l1_struct_0(D_244) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_285])).
% 5.91/2.14  tff(c_294, plain, (![D_244]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_244)) | ~l1_struct_0(D_244) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_287])).
% 5.91/2.14  tff(c_325, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_294])).
% 5.91/2.14  tff(c_328, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_325])).
% 5.91/2.14  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_328])).
% 5.91/2.14  tff(c_334, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_294])).
% 5.91/2.14  tff(c_289, plain, (![D_244]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_244)) | ~l1_struct_0(D_244) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_285])).
% 5.91/2.14  tff(c_297, plain, (![D_244]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_244)) | ~l1_struct_0(D_244) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_289])).
% 5.91/2.14  tff(c_336, plain, (![D_244]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_244)) | ~l1_struct_0(D_244) | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_297])).
% 5.91/2.14  tff(c_337, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_336])).
% 5.91/2.14  tff(c_340, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_337])).
% 5.91/2.14  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_340])).
% 5.91/2.14  tff(c_346, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_336])).
% 5.91/2.14  tff(c_594, plain, (![F_290, B_292, A_288, C_289, D_291]: (r1_funct_2(A_288, B_292, C_289, D_291, F_290, F_290) | ~m1_subset_1(F_290, k1_zfmisc_1(k2_zfmisc_1(C_289, D_291))) | ~v1_funct_2(F_290, C_289, D_291) | ~m1_subset_1(F_290, k1_zfmisc_1(k2_zfmisc_1(A_288, B_292))) | ~v1_funct_2(F_290, A_288, B_292) | ~v1_funct_1(F_290) | v1_xboole_0(D_291) | v1_xboole_0(B_292))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.91/2.14  tff(c_598, plain, (![A_288, B_292]: (r1_funct_2(A_288, B_292, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_7', '#skF_7') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_288, B_292))) | ~v1_funct_2('#skF_7', A_288, B_292) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_292))), inference(resolution, [status(thm)], [c_48, c_594])).
% 5.91/2.14  tff(c_606, plain, (![A_288, B_292]: (r1_funct_2(A_288, B_292, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_7', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_288, B_292))) | ~v1_funct_2('#skF_7', A_288, B_292) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_292))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_598])).
% 5.91/2.14  tff(c_618, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_606])).
% 5.91/2.14  tff(c_621, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_618, c_20])).
% 5.91/2.14  tff(c_624, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_621])).
% 5.91/2.14  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_624])).
% 5.91/2.14  tff(c_628, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_606])).
% 5.91/2.14  tff(c_740, plain, (![D_328, B_329, F_327, E_326, C_325, A_324]: (F_327=E_326 | ~r1_funct_2(A_324, B_329, C_325, D_328, E_326, F_327) | ~m1_subset_1(F_327, k1_zfmisc_1(k2_zfmisc_1(C_325, D_328))) | ~v1_funct_2(F_327, C_325, D_328) | ~v1_funct_1(F_327) | ~m1_subset_1(E_326, k1_zfmisc_1(k2_zfmisc_1(A_324, B_329))) | ~v1_funct_2(E_326, A_324, B_329) | ~v1_funct_1(E_326) | v1_xboole_0(D_328) | v1_xboole_0(B_329))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.91/2.14  tff(c_748, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_102, c_740])).
% 5.91/2.14  tff(c_766, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_100, c_52, c_50, c_48, c_748])).
% 5.91/2.14  tff(c_767, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_628, c_766])).
% 5.91/2.14  tff(c_86, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_101, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_86])).
% 5.91/2.14  tff(c_188, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_101])).
% 5.91/2.14  tff(c_775, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_767, c_188])).
% 5.91/2.14  tff(c_291, plain, (![D_244]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_244)) | ~l1_struct_0(D_244) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_285])).
% 5.91/2.14  tff(c_300, plain, (![D_244]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_244)) | ~l1_struct_0(D_244) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_291])).
% 5.91/2.14  tff(c_352, plain, (![D_244]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_244)) | ~l1_struct_0(D_244) | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_300])).
% 5.91/2.14  tff(c_353, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_352])).
% 5.91/2.14  tff(c_372, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_353])).
% 5.91/2.14  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_372])).
% 5.91/2.14  tff(c_378, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_352])).
% 5.91/2.14  tff(c_520, plain, (![A_279, B_280, C_281, D_282]: (v1_funct_2(k2_tmap_1(A_279, B_280, C_281, D_282), u1_struct_0(D_282), u1_struct_0(B_280)) | ~l1_struct_0(D_282) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_279), u1_struct_0(B_280)))) | ~v1_funct_2(C_281, u1_struct_0(A_279), u1_struct_0(B_280)) | ~v1_funct_1(C_281) | ~l1_struct_0(B_280) | ~l1_struct_0(A_279))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.91/2.14  tff(c_524, plain, (![D_282]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_282), u1_struct_0(D_282), u1_struct_0('#skF_2')) | ~l1_struct_0(D_282) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_520])).
% 5.91/2.14  tff(c_541, plain, (![D_283]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_283), u1_struct_0(D_283), u1_struct_0('#skF_2')) | ~l1_struct_0(D_283))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_346, c_64, c_99, c_524])).
% 5.91/2.14  tff(c_442, plain, (![A_274, B_275, C_276, D_277]: (m1_subset_1(k2_tmap_1(A_274, B_275, C_276, D_277), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_277), u1_struct_0(B_275)))) | ~l1_struct_0(D_277) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_274), u1_struct_0(B_275)))) | ~v1_funct_2(C_276, u1_struct_0(A_274), u1_struct_0(B_275)) | ~v1_funct_1(C_276) | ~l1_struct_0(B_275) | ~l1_struct_0(A_274))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.91/2.14  tff(c_333, plain, (![D_244]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_244)) | ~l1_struct_0(D_244))), inference(splitRight, [status(thm)], [c_294])).
% 5.91/2.14  tff(c_349, plain, (![D_244]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_244)) | ~l1_struct_0(D_244))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_333])).
% 5.91/2.14  tff(c_92, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.91/2.14  tff(c_97, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_92])).
% 5.91/2.14  tff(c_241, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_188, c_97])).
% 5.91/2.14  tff(c_301, plain, (![D_245, C_246, A_247, B_248]: (D_245=C_246 | ~r2_funct_2(A_247, B_248, C_246, D_245) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))) | ~v1_funct_2(D_245, A_247, B_248) | ~v1_funct_1(D_245) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))) | ~v1_funct_2(C_246, A_247, B_248) | ~v1_funct_1(C_246))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.91/2.14  tff(c_303, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_241, c_301])).
% 5.91/2.14  tff(c_312, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_303])).
% 5.91/2.14  tff(c_380, plain, (~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_312])).
% 5.91/2.14  tff(c_383, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_349, c_380])).
% 5.91/2.14  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_378, c_383])).
% 5.91/2.14  tff(c_388, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_312])).
% 5.91/2.14  tff(c_390, plain, (~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_388])).
% 5.91/2.14  tff(c_449, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_442, c_390])).
% 5.91/2.14  tff(c_470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_334, c_346, c_64, c_99, c_100, c_378, c_449])).
% 5.91/2.14  tff(c_471, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_388])).
% 5.91/2.14  tff(c_506, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_471])).
% 5.91/2.14  tff(c_544, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_541, c_506])).
% 5.91/2.14  tff(c_548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_378, c_544])).
% 5.91/2.14  tff(c_549, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_471])).
% 5.91/2.14  tff(c_209, plain, (![A_229, B_230, C_231, D_232]: (k2_partfun1(A_229, B_230, C_231, D_232)=k7_relat_1(C_231, D_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))) | ~v1_funct_1(C_231))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.91/2.14  tff(c_211, plain, (![D_232]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_232)=k7_relat_1('#skF_5', D_232) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_100, c_209])).
% 5.91/2.14  tff(c_218, plain, (![D_232]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_232)=k7_relat_1('#skF_5', D_232))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_211])).
% 5.91/2.14  tff(c_859, plain, (![A_339, B_340, C_341, D_342]: (k2_partfun1(u1_struct_0(A_339), u1_struct_0(B_340), C_341, u1_struct_0(D_342))=k2_tmap_1(A_339, B_340, C_341, D_342) | ~m1_pre_topc(D_342, A_339) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_339), u1_struct_0(B_340)))) | ~v1_funct_2(C_341, u1_struct_0(A_339), u1_struct_0(B_340)) | ~v1_funct_1(C_341) | ~l1_pre_topc(B_340) | ~v2_pre_topc(B_340) | v2_struct_0(B_340) | ~l1_pre_topc(A_339) | ~v2_pre_topc(A_339) | v2_struct_0(A_339))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.91/2.14  tff(c_863, plain, (![D_342]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_342))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_342) | ~m1_pre_topc(D_342, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_859])).
% 5.91/2.14  tff(c_869, plain, (![D_342]: (k7_relat_1('#skF_5', u1_struct_0(D_342))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_342) | ~m1_pre_topc(D_342, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_76, c_74, c_64, c_99, c_218, c_863])).
% 5.91/2.14  tff(c_875, plain, (![D_343]: (k7_relat_1('#skF_5', u1_struct_0(D_343))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_343) | ~m1_pre_topc(D_343, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_78, c_869])).
% 5.91/2.14  tff(c_122, plain, (![C_214, A_215, B_216]: (v1_relat_1(C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.91/2.14  tff(c_132, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_122])).
% 5.91/2.14  tff(c_149, plain, (![C_222, A_223, B_224]: (v4_relat_1(C_222, A_223) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.91/2.14  tff(c_159, plain, (v4_relat_1('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_149])).
% 5.91/2.14  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.91/2.14  tff(c_164, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_159, c_2])).
% 5.91/2.14  tff(c_167, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_164])).
% 5.91/2.14  tff(c_881, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_875, c_167])).
% 5.91/2.14  tff(c_890, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_881])).
% 5.91/2.14  tff(c_1067, plain, (![D_387, A_389, C_390, B_388, E_391]: (r2_funct_2(u1_struct_0(C_390), u1_struct_0(B_388), k3_tmap_1(A_389, B_388, D_387, C_390, k2_tmap_1(A_389, B_388, E_391, D_387)), k2_tmap_1(A_389, B_388, E_391, C_390)) | ~m1_pre_topc(C_390, D_387) | ~m1_subset_1(E_391, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_389), u1_struct_0(B_388)))) | ~v1_funct_2(E_391, u1_struct_0(A_389), u1_struct_0(B_388)) | ~v1_funct_1(E_391) | ~m1_pre_topc(D_387, A_389) | v2_struct_0(D_387) | ~m1_pre_topc(C_390, A_389) | v2_struct_0(C_390) | ~l1_pre_topc(B_388) | ~v2_pre_topc(B_388) | v2_struct_0(B_388) | ~l1_pre_topc(A_389) | ~v2_pre_topc(A_389) | v2_struct_0(A_389))), inference(cnfTransformation, [status(thm)], [f_217])).
% 5.91/2.14  tff(c_1072, plain, (![C_390]: (r2_funct_2(u1_struct_0(C_390), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_390, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_390)) | ~m1_pre_topc(C_390, '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_390, '#skF_4') | v2_struct_0(C_390) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_890, c_1067])).
% 5.91/2.14  tff(c_1084, plain, (![C_390]: (r2_funct_2(u1_struct_0(C_390), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_390, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_390)) | ~m1_pre_topc(C_390, '#skF_4') | v2_struct_0(C_390) | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_76, c_74, c_98, c_64, c_99, c_100, c_1072])).
% 5.91/2.14  tff(c_1100, plain, (![C_394]: (r2_funct_2(u1_struct_0(C_394), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_394, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_394)) | ~m1_pre_topc(C_394, '#skF_4') | v2_struct_0(C_394))), inference(negUnitSimplification, [status(thm)], [c_68, c_78, c_1084])).
% 5.91/2.14  tff(c_1108, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_549, c_1100])).
% 5.91/2.14  tff(c_1114, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1108])).
% 5.91/2.14  tff(c_1116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_775, c_1114])).
% 5.91/2.14  tff(c_1118, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_101])).
% 5.91/2.14  tff(c_1296, plain, (![D_422, C_423, A_424, B_425]: (D_422=C_423 | ~r2_funct_2(A_424, B_425, C_423, D_422) | ~m1_subset_1(D_422, k1_zfmisc_1(k2_zfmisc_1(A_424, B_425))) | ~v1_funct_2(D_422, A_424, B_425) | ~v1_funct_1(D_422) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_424, B_425))) | ~v1_funct_2(C_423, A_424, B_425) | ~v1_funct_1(C_423))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.91/2.14  tff(c_1304, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'))), inference(resolution, [status(thm)], [c_1118, c_1296])).
% 5.91/2.14  tff(c_1319, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1304])).
% 5.91/2.14  tff(c_1561, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1490, c_1490, c_1490, c_1319])).
% 5.91/2.14  tff(c_1562, plain, (~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1561])).
% 5.91/2.14  tff(c_1582, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1579, c_1562])).
% 5.91/2.14  tff(c_1585, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_98, c_96, c_1582])).
% 5.91/2.14  tff(c_1587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1585])).
% 5.91/2.14  tff(c_1589, plain, (v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_1561])).
% 5.91/2.14  tff(c_1498, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1118])).
% 5.91/2.14  tff(c_14, plain, (![D_16, C_15, A_13, B_14]: (D_16=C_15 | ~r2_funct_2(A_13, B_14, C_15, D_16) | ~m1_subset_1(D_16, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(D_16, A_13, B_14) | ~v1_funct_1(D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.91/2.14  tff(c_1539, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_1498, c_14])).
% 5.91/2.14  tff(c_1542, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1539])).
% 5.91/2.14  tff(c_1591, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1542])).
% 5.91/2.14  tff(c_1592, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1591])).
% 5.91/2.14  tff(c_1706, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1703, c_1592])).
% 5.91/2.14  tff(c_1709, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_98, c_96, c_1706])).
% 5.91/2.14  tff(c_1711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1709])).
% 5.91/2.14  tff(c_1712, plain, (~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_1591])).
% 5.91/2.14  tff(c_1714, plain, (~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1712])).
% 5.91/2.14  tff(c_1836, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1829, c_1714])).
% 5.91/2.14  tff(c_1868, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_76, c_74, c_98, c_96, c_64, c_99, c_100, c_1836])).
% 5.91/2.14  tff(c_1870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_78, c_1868])).
% 5.91/2.14  tff(c_1871, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_1712])).
% 5.91/2.14  tff(c_1144, plain, (![A_399, B_400, C_401, D_402]: (k2_partfun1(A_399, B_400, C_401, D_402)=k7_relat_1(C_401, D_402) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_399, B_400))) | ~v1_funct_1(C_401))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.91/2.14  tff(c_1146, plain, (![D_402]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_402)=k7_relat_1('#skF_5', D_402) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_100, c_1144])).
% 5.91/2.14  tff(c_1153, plain, (![D_402]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_402)=k7_relat_1('#skF_5', D_402))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1146])).
% 5.91/2.14  tff(c_1909, plain, (![A_539, B_540, C_541, D_542]: (k2_partfun1(u1_struct_0(A_539), u1_struct_0(B_540), C_541, u1_struct_0(D_542))=k2_tmap_1(A_539, B_540, C_541, D_542) | ~m1_pre_topc(D_542, A_539) | ~m1_subset_1(C_541, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_539), u1_struct_0(B_540)))) | ~v1_funct_2(C_541, u1_struct_0(A_539), u1_struct_0(B_540)) | ~v1_funct_1(C_541) | ~l1_pre_topc(B_540) | ~v2_pre_topc(B_540) | v2_struct_0(B_540) | ~l1_pre_topc(A_539) | ~v2_pre_topc(A_539) | v2_struct_0(A_539))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.91/2.14  tff(c_1913, plain, (![D_542]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_542))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_542) | ~m1_pre_topc(D_542, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_1909])).
% 5.91/2.14  tff(c_1919, plain, (![D_542]: (k7_relat_1('#skF_5', u1_struct_0(D_542))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_542) | ~m1_pre_topc(D_542, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_76, c_74, c_64, c_99, c_1153, c_1913])).
% 5.91/2.14  tff(c_1925, plain, (![D_543]: (k7_relat_1('#skF_5', u1_struct_0(D_543))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_543) | ~m1_pre_topc(D_543, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_78, c_1919])).
% 5.91/2.14  tff(c_1931, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1925, c_167])).
% 5.91/2.14  tff(c_1940, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1931])).
% 5.91/2.14  tff(c_2089, plain, (![C_572, D_569, A_571, B_570, E_573]: (r2_funct_2(u1_struct_0(C_572), u1_struct_0(B_570), k3_tmap_1(A_571, B_570, D_569, C_572, k2_tmap_1(A_571, B_570, E_573, D_569)), k2_tmap_1(A_571, B_570, E_573, C_572)) | ~m1_pre_topc(C_572, D_569) | ~m1_subset_1(E_573, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_571), u1_struct_0(B_570)))) | ~v1_funct_2(E_573, u1_struct_0(A_571), u1_struct_0(B_570)) | ~v1_funct_1(E_573) | ~m1_pre_topc(D_569, A_571) | v2_struct_0(D_569) | ~m1_pre_topc(C_572, A_571) | v2_struct_0(C_572) | ~l1_pre_topc(B_570) | ~v2_pre_topc(B_570) | v2_struct_0(B_570) | ~l1_pre_topc(A_571) | ~v2_pre_topc(A_571) | v2_struct_0(A_571))), inference(cnfTransformation, [status(thm)], [f_217])).
% 5.91/2.14  tff(c_2094, plain, (![C_572]: (r2_funct_2(u1_struct_0(C_572), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_572, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_572)) | ~m1_pre_topc(C_572, '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_572, '#skF_4') | v2_struct_0(C_572) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1940, c_2089])).
% 5.91/2.14  tff(c_2100, plain, (![C_572]: (r2_funct_2(u1_struct_0(C_572), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_572, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_572)) | ~m1_pre_topc(C_572, '#skF_4') | v2_struct_0(C_572) | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_76, c_74, c_98, c_64, c_99, c_100, c_2094])).
% 5.91/2.14  tff(c_2105, plain, (![C_574]: (r2_funct_2(u1_struct_0(C_574), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_574, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_574)) | ~m1_pre_topc(C_574, '#skF_4') | v2_struct_0(C_574))), inference(negUnitSimplification, [status(thm)], [c_68, c_78, c_2100])).
% 5.91/2.14  tff(c_2113, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1871, c_2105])).
% 5.91/2.14  tff(c_2119, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2113])).
% 5.91/2.14  tff(c_2120, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2119])).
% 5.91/2.14  tff(c_2122, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_2120, c_14])).
% 5.91/2.14  tff(c_2125, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2122])).
% 5.91/2.14  tff(c_2143, plain, (~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2125])).
% 5.91/2.14  tff(c_2165, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1278, c_2143])).
% 5.91/2.14  tff(c_2169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1228, c_2165])).
% 5.91/2.14  tff(c_2170, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_2125])).
% 5.91/2.14  tff(c_2172, plain, (~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_2170])).
% 5.91/2.14  tff(c_2190, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_2172])).
% 5.91/2.14  tff(c_2194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1238, c_1272, c_64, c_99, c_100, c_1228, c_2190])).
% 5.91/2.14  tff(c_2195, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_2170])).
% 5.91/2.14  tff(c_2321, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2195])).
% 5.91/2.14  tff(c_2324, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1329, c_2321])).
% 5.91/2.14  tff(c_2328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1228, c_2324])).
% 5.91/2.14  tff(c_2329, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_2195])).
% 5.91/2.14  tff(c_1117, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_101])).
% 5.91/2.14  tff(c_2345, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2329, c_1117])).
% 5.91/2.14  tff(c_2355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1202, c_2345])).
% 5.91/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.14  
% 5.91/2.14  Inference rules
% 5.91/2.14  ----------------------
% 5.91/2.14  #Ref     : 0
% 5.91/2.14  #Sup     : 425
% 5.91/2.14  #Fact    : 0
% 5.91/2.14  #Define  : 0
% 5.91/2.14  #Split   : 25
% 5.91/2.14  #Chain   : 0
% 5.91/2.14  #Close   : 0
% 5.91/2.14  
% 5.91/2.14  Ordering : KBO
% 5.91/2.14  
% 5.91/2.14  Simplification rules
% 5.91/2.14  ----------------------
% 5.91/2.14  #Subsume      : 22
% 5.91/2.14  #Demod        : 921
% 5.91/2.14  #Tautology    : 176
% 5.91/2.14  #SimpNegUnit  : 86
% 5.91/2.14  #BackRed      : 48
% 5.91/2.14  
% 5.91/2.14  #Partial instantiations: 0
% 5.91/2.14  #Strategies tried      : 1
% 5.91/2.14  
% 5.91/2.14  Timing (in seconds)
% 5.91/2.14  ----------------------
% 5.91/2.14  Preprocessing        : 0.49
% 5.91/2.14  Parsing              : 0.27
% 5.91/2.14  CNF conversion       : 0.05
% 5.91/2.14  Main loop            : 0.81
% 5.91/2.14  Inferencing          : 0.29
% 5.91/2.14  Reduction            : 0.28
% 5.91/2.14  Demodulation         : 0.21
% 5.91/2.14  BG Simplification    : 0.04
% 5.91/2.14  Subsumption          : 0.14
% 5.91/2.14  Abstraction          : 0.03
% 5.91/2.14  MUC search           : 0.00
% 5.91/2.14  Cooper               : 0.00
% 5.91/2.14  Total                : 1.39
% 5.91/2.14  Index Insertion      : 0.00
% 5.91/2.14  Index Deletion       : 0.00
% 5.91/2.14  Index Matching       : 0.00
% 5.91/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
