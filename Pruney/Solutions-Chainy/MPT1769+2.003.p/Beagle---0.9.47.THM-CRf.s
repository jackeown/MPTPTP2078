%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:17 EST 2020

% Result     : Theorem 6.16s
% Output     : CNFRefutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :  305 (3619 expanded)
%              Number of leaves         :   45 (1317 expanded)
%              Depth                    :   27
%              Number of atoms          : 1027 (32080 expanded)
%              Number of equality atoms :   67 (1841 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_295,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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

tff(f_226,axiom,(
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
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),F,k2_tmap_1(A,B,E,C))
                              & m1_pre_topc(D,C) )
                           => r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,C,D,F),k2_tmap_1(A,B,E,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_1241,plain,(
    ! [A_446,B_447,D_448] :
      ( r2_funct_2(A_446,B_447,D_448,D_448)
      | ~ m1_subset_1(D_448,k1_zfmisc_1(k2_zfmisc_1(A_446,B_447)))
      | ~ v1_funct_2(D_448,A_446,B_447)
      | ~ v1_funct_1(D_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1247,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_1241])).

tff(c_1256,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1247])).

tff(c_46,plain,(
    '#skF_1' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_80,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_95,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_80])).

tff(c_70,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_96,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_70])).

tff(c_108,plain,(
    ! [B_243,A_244] :
      ( l1_pre_topc(B_243)
      | ~ m1_pre_topc(B_243,A_244)
      | ~ l1_pre_topc(A_244) ) ),
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

tff(c_1257,plain,(
    ! [A_449,B_450,C_451,D_452] :
      ( v1_funct_1(k2_tmap_1(A_449,B_450,C_451,D_452))
      | ~ l1_struct_0(D_452)
      | ~ m1_subset_1(C_451,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_449),u1_struct_0(B_450))))
      | ~ v1_funct_2(C_451,u1_struct_0(A_449),u1_struct_0(B_450))
      | ~ v1_funct_1(C_451)
      | ~ l1_struct_0(B_450)
      | ~ l1_struct_0(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1263,plain,(
    ! [D_452] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_452))
      | ~ l1_struct_0(D_452)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_1257])).

tff(c_1272,plain,(
    ! [D_452] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_452))
      | ~ l1_struct_0(D_452)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1263])).

tff(c_1273,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1272])).

tff(c_1277,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1273])).

tff(c_1281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_1277])).

tff(c_1283,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1272])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_1282,plain,(
    ! [D_452] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_452))
      | ~ l1_struct_0(D_452) ) ),
    inference(splitRight,[status(thm)],[c_1272])).

tff(c_1284,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1282])).

tff(c_1287,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1284])).

tff(c_1291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1287])).

tff(c_1293,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1282])).

tff(c_52,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_50,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_1261,plain,(
    ! [D_452] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_452))
      | ~ l1_struct_0(D_452)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_1257])).

tff(c_1269,plain,(
    ! [D_452] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_452))
      | ~ l1_struct_0(D_452)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1261])).

tff(c_1320,plain,(
    ! [D_452] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_452))
      | ~ l1_struct_0(D_452)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_1269])).

tff(c_1321,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1320])).

tff(c_1324,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_1321])).

tff(c_1328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1324])).

tff(c_1330,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1320])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_62,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_99,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_62])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_100,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_60])).

tff(c_1340,plain,(
    ! [A_459,B_460,C_461,D_462] :
      ( v1_funct_2(k2_tmap_1(A_459,B_460,C_461,D_462),u1_struct_0(D_462),u1_struct_0(B_460))
      | ~ l1_struct_0(D_462)
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_459),u1_struct_0(B_460))))
      | ~ v1_funct_2(C_461,u1_struct_0(A_459),u1_struct_0(B_460))
      | ~ v1_funct_1(C_461)
      | ~ l1_struct_0(B_460)
      | ~ l1_struct_0(A_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1342,plain,(
    ! [D_462] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_462),u1_struct_0(D_462),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_462)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_1340])).

tff(c_1349,plain,(
    ! [D_462] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_462),u1_struct_0(D_462),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_1293,c_64,c_99,c_1342])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_1259,plain,(
    ! [D_452] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_452))
      | ~ l1_struct_0(D_452)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_1257])).

tff(c_1266,plain,(
    ! [D_452] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_452))
      | ~ l1_struct_0(D_452)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_1259])).

tff(c_1332,plain,(
    ! [D_452] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_452))
      | ~ l1_struct_0(D_452)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_1266])).

tff(c_1333,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1332])).

tff(c_1335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_1333])).

tff(c_1336,plain,(
    ! [D_452] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_452))
      | ~ l1_struct_0(D_452) ) ),
    inference(splitRight,[status(thm)],[c_1332])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_1243,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_1241])).

tff(c_1250,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_1243])).

tff(c_1376,plain,(
    ! [B_473,F_471,C_470,D_472,A_469] :
      ( r1_funct_2(A_469,B_473,C_470,D_472,F_471,F_471)
      | ~ m1_subset_1(F_471,k1_zfmisc_1(k2_zfmisc_1(C_470,D_472)))
      | ~ v1_funct_2(F_471,C_470,D_472)
      | ~ m1_subset_1(F_471,k1_zfmisc_1(k2_zfmisc_1(A_469,B_473)))
      | ~ v1_funct_2(F_471,A_469,B_473)
      | ~ v1_funct_1(F_471)
      | v1_xboole_0(D_472)
      | v1_xboole_0(B_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1378,plain,(
    ! [A_469,B_473] :
      ( r1_funct_2(A_469,B_473,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_469,B_473)))
      | ~ v1_funct_2('#skF_5',A_469,B_473)
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_473) ) ),
    inference(resolution,[status(thm)],[c_100,c_1376])).

tff(c_1385,plain,(
    ! [A_469,B_473] :
      ( r1_funct_2(A_469,B_473,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_469,B_473)))
      | ~ v1_funct_2('#skF_5',A_469,B_473)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_473) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_1378])).

tff(c_1392,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1385])).

tff(c_20,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1395,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1392,c_20])).

tff(c_1398,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_1395])).

tff(c_1400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1398])).

tff(c_1402,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1385])).

tff(c_44,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_102,plain,(
    r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_2343,plain,(
    ! [A_621,C_622,B_626,D_625,E_623,F_624] :
      ( F_624 = E_623
      | ~ r1_funct_2(A_621,B_626,C_622,D_625,E_623,F_624)
      | ~ m1_subset_1(F_624,k1_zfmisc_1(k2_zfmisc_1(C_622,D_625)))
      | ~ v1_funct_2(F_624,C_622,D_625)
      | ~ v1_funct_1(F_624)
      | ~ m1_subset_1(E_623,k1_zfmisc_1(k2_zfmisc_1(A_621,B_626)))
      | ~ v1_funct_2(E_623,A_621,B_626)
      | ~ v1_funct_1(E_623)
      | v1_xboole_0(D_625)
      | v1_xboole_0(B_626) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2351,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_102,c_2343])).

tff(c_2369,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_100,c_52,c_50,c_48,c_2351])).

tff(c_2370,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1402,c_2369])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_82,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_94,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_82])).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_98,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_66])).

tff(c_2274,plain,(
    ! [B_615,A_612,D_614,E_613,C_616] :
      ( v1_funct_2(k3_tmap_1(A_612,B_615,C_616,D_614,E_613),u1_struct_0(D_614),u1_struct_0(B_615))
      | ~ m1_subset_1(E_613,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_616),u1_struct_0(B_615))))
      | ~ v1_funct_2(E_613,u1_struct_0(C_616),u1_struct_0(B_615))
      | ~ v1_funct_1(E_613)
      | ~ m1_pre_topc(D_614,A_612)
      | ~ m1_pre_topc(C_616,A_612)
      | ~ l1_pre_topc(B_615)
      | ~ v2_pre_topc(B_615)
      | v2_struct_0(B_615)
      | ~ l1_pre_topc(A_612)
      | ~ v2_pre_topc(A_612)
      | v2_struct_0(A_612) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2280,plain,(
    ! [A_612,D_614] :
      ( v1_funct_2(k3_tmap_1(A_612,'#skF_2','#skF_4',D_614,'#skF_5'),u1_struct_0(D_614),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_614,A_612)
      | ~ m1_pre_topc('#skF_4',A_612)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_612)
      | ~ v2_pre_topc(A_612)
      | v2_struct_0(A_612) ) ),
    inference(resolution,[status(thm)],[c_100,c_2274])).

tff(c_2290,plain,(
    ! [A_612,D_614] :
      ( v1_funct_2(k3_tmap_1(A_612,'#skF_2','#skF_4',D_614,'#skF_5'),u1_struct_0(D_614),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_614,A_612)
      | ~ m1_pre_topc('#skF_4',A_612)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_612)
      | ~ v2_pre_topc(A_612)
      | v2_struct_0(A_612) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_99,c_2280])).

tff(c_2303,plain,(
    ! [A_619,D_620] :
      ( v1_funct_2(k3_tmap_1(A_619,'#skF_2','#skF_4',D_620,'#skF_5'),u1_struct_0(D_620),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_620,A_619)
      | ~ m1_pre_topc('#skF_4',A_619)
      | ~ l1_pre_topc(A_619)
      | ~ v2_pre_topc(A_619)
      | v2_struct_0(A_619) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2290])).

tff(c_2003,plain,(
    ! [E_583,C_582,A_581,D_585,F_584,B_586] :
      ( F_584 = E_583
      | ~ r1_funct_2(A_581,B_586,C_582,D_585,E_583,F_584)
      | ~ m1_subset_1(F_584,k1_zfmisc_1(k2_zfmisc_1(C_582,D_585)))
      | ~ v1_funct_2(F_584,C_582,D_585)
      | ~ v1_funct_1(F_584)
      | ~ m1_subset_1(E_583,k1_zfmisc_1(k2_zfmisc_1(A_581,B_586)))
      | ~ v1_funct_2(E_583,A_581,B_586)
      | ~ v1_funct_1(E_583)
      | v1_xboole_0(D_585)
      | v1_xboole_0(B_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2011,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_102,c_2003])).

tff(c_2029,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_100,c_52,c_50,c_48,c_2011])).

tff(c_2030,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1402,c_2029])).

tff(c_1563,plain,(
    ! [B_511,E_509,D_510,A_508,C_512] :
      ( v1_funct_1(k3_tmap_1(A_508,B_511,C_512,D_510,E_509))
      | ~ m1_subset_1(E_509,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_512),u1_struct_0(B_511))))
      | ~ v1_funct_2(E_509,u1_struct_0(C_512),u1_struct_0(B_511))
      | ~ v1_funct_1(E_509)
      | ~ m1_pre_topc(D_510,A_508)
      | ~ m1_pre_topc(C_512,A_508)
      | ~ l1_pre_topc(B_511)
      | ~ v2_pre_topc(B_511)
      | v2_struct_0(B_511)
      | ~ l1_pre_topc(A_508)
      | ~ v2_pre_topc(A_508)
      | v2_struct_0(A_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1567,plain,(
    ! [A_508,D_510] :
      ( v1_funct_1(k3_tmap_1(A_508,'#skF_2','#skF_4',D_510,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_510,A_508)
      | ~ m1_pre_topc('#skF_4',A_508)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_508)
      | ~ v2_pre_topc(A_508)
      | v2_struct_0(A_508) ) ),
    inference(resolution,[status(thm)],[c_100,c_1563])).

tff(c_1573,plain,(
    ! [A_508,D_510] :
      ( v1_funct_1(k3_tmap_1(A_508,'#skF_2','#skF_4',D_510,'#skF_5'))
      | ~ m1_pre_topc(D_510,A_508)
      | ~ m1_pre_topc('#skF_4',A_508)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_508)
      | ~ v2_pre_topc(A_508)
      | v2_struct_0(A_508) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_99,c_1567])).

tff(c_1584,plain,(
    ! [A_514,D_515] :
      ( v1_funct_1(k3_tmap_1(A_514,'#skF_2','#skF_4',D_515,'#skF_5'))
      | ~ m1_pre_topc(D_515,A_514)
      | ~ m1_pre_topc('#skF_4',A_514)
      | ~ l1_pre_topc(A_514)
      | ~ v2_pre_topc(A_514)
      | v2_struct_0(A_514) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1573])).

tff(c_1459,plain,(
    ! [E_493,A_491,D_495,F_494,C_492,B_496] :
      ( F_494 = E_493
      | ~ r1_funct_2(A_491,B_496,C_492,D_495,E_493,F_494)
      | ~ m1_subset_1(F_494,k1_zfmisc_1(k2_zfmisc_1(C_492,D_495)))
      | ~ v1_funct_2(F_494,C_492,D_495)
      | ~ v1_funct_1(F_494)
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1(A_491,B_496)))
      | ~ v1_funct_2(E_493,A_491,B_496)
      | ~ v1_funct_1(E_493)
      | v1_xboole_0(D_495)
      | v1_xboole_0(B_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1467,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_102,c_1459])).

tff(c_1485,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_100,c_52,c_50,c_48,c_1467])).

tff(c_1486,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1402,c_1485])).

tff(c_285,plain,(
    ! [A_273,B_274,C_275,D_276] :
      ( v1_funct_1(k2_tmap_1(A_273,B_274,C_275,D_276))
      | ~ l1_struct_0(D_276)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_273),u1_struct_0(B_274))))
      | ~ v1_funct_2(C_275,u1_struct_0(A_273),u1_struct_0(B_274))
      | ~ v1_funct_1(C_275)
      | ~ l1_struct_0(B_274)
      | ~ l1_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_287,plain,(
    ! [D_276] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_276))
      | ~ l1_struct_0(D_276)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_285])).

tff(c_294,plain,(
    ! [D_276] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_276))
      | ~ l1_struct_0(D_276)
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
    ! [D_276] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_276))
      | ~ l1_struct_0(D_276)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_285])).

tff(c_297,plain,(
    ! [D_276] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_276))
      | ~ l1_struct_0(D_276)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_289])).

tff(c_336,plain,(
    ! [D_276] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_276))
      | ~ l1_struct_0(D_276)
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
    ! [F_322,A_320,C_321,D_323,B_324] :
      ( r1_funct_2(A_320,B_324,C_321,D_323,F_322,F_322)
      | ~ m1_subset_1(F_322,k1_zfmisc_1(k2_zfmisc_1(C_321,D_323)))
      | ~ v1_funct_2(F_322,C_321,D_323)
      | ~ m1_subset_1(F_322,k1_zfmisc_1(k2_zfmisc_1(A_320,B_324)))
      | ~ v1_funct_2(F_322,A_320,B_324)
      | ~ v1_funct_1(F_322)
      | v1_xboole_0(D_323)
      | v1_xboole_0(B_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_598,plain,(
    ! [A_320,B_324] :
      ( r1_funct_2(A_320,B_324,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_7','#skF_7')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_320,B_324)))
      | ~ v1_funct_2('#skF_7',A_320,B_324)
      | ~ v1_funct_1('#skF_7')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_324) ) ),
    inference(resolution,[status(thm)],[c_48,c_594])).

tff(c_606,plain,(
    ! [A_320,B_324] :
      ( r1_funct_2(A_320,B_324,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_7','#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_320,B_324)))
      | ~ v1_funct_2('#skF_7',A_320,B_324)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_324) ) ),
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
    ! [F_359,C_357,B_361,A_356,E_358,D_360] :
      ( F_359 = E_358
      | ~ r1_funct_2(A_356,B_361,C_357,D_360,E_358,F_359)
      | ~ m1_subset_1(F_359,k1_zfmisc_1(k2_zfmisc_1(C_357,D_360)))
      | ~ v1_funct_2(F_359,C_357,D_360)
      | ~ v1_funct_1(F_359)
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(A_356,B_361)))
      | ~ v1_funct_2(E_358,A_356,B_361)
      | ~ v1_funct_1(E_358)
      | v1_xboole_0(D_360)
      | v1_xboole_0(B_361) ) ),
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
    inference(cnfTransformation,[status(thm)],[f_295])).

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

tff(c_225,plain,(
    ! [A_265,B_266,D_267] :
      ( r2_funct_2(A_265,B_266,D_267,D_267)
      | ~ m1_subset_1(D_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ v1_funct_2(D_267,A_265,B_266)
      | ~ v1_funct_1(D_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_227,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_225])).

tff(c_234,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_227])).

tff(c_291,plain,(
    ! [D_276] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_276))
      | ~ l1_struct_0(D_276)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_285])).

tff(c_300,plain,(
    ! [D_276] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_276))
      | ~ l1_struct_0(D_276)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_291])).

tff(c_352,plain,(
    ! [D_276] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_276))
      | ~ l1_struct_0(D_276)
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
    ! [A_311,B_312,C_313,D_314] :
      ( v1_funct_2(k2_tmap_1(A_311,B_312,C_313,D_314),u1_struct_0(D_314),u1_struct_0(B_312))
      | ~ l1_struct_0(D_314)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_311),u1_struct_0(B_312))))
      | ~ v1_funct_2(C_313,u1_struct_0(A_311),u1_struct_0(B_312))
      | ~ v1_funct_1(C_313)
      | ~ l1_struct_0(B_312)
      | ~ l1_struct_0(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_524,plain,(
    ! [D_314] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_314),u1_struct_0(D_314),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_314)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_520])).

tff(c_541,plain,(
    ! [D_315] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_315),u1_struct_0(D_315),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_315) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_346,c_64,c_99,c_524])).

tff(c_442,plain,(
    ! [A_306,B_307,C_308,D_309] :
      ( m1_subset_1(k2_tmap_1(A_306,B_307,C_308,D_309),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_309),u1_struct_0(B_307))))
      | ~ l1_struct_0(D_309)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_306),u1_struct_0(B_307))))
      | ~ v1_funct_2(C_308,u1_struct_0(A_306),u1_struct_0(B_307))
      | ~ v1_funct_1(C_308)
      | ~ l1_struct_0(B_307)
      | ~ l1_struct_0(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_333,plain,(
    ! [D_276] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_276))
      | ~ l1_struct_0(D_276) ) ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_349,plain,(
    ! [D_276] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_276))
      | ~ l1_struct_0(D_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_333])).

tff(c_92,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_97,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_92])).

tff(c_241,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_97])).

tff(c_301,plain,(
    ! [D_277,C_278,A_279,B_280] :
      ( D_277 = C_278
      | ~ r2_funct_2(A_279,B_280,C_278,D_277)
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280)))
      | ~ v1_funct_2(D_277,A_279,B_280)
      | ~ v1_funct_1(D_277)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280)))
      | ~ v1_funct_2(C_278,A_279,B_280)
      | ~ v1_funct_1(C_278) ) ),
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
    ! [A_261,B_262,C_263,D_264] :
      ( k2_partfun1(A_261,B_262,C_263,D_264) = k7_relat_1(C_263,D_264)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_1(C_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_211,plain,(
    ! [D_264] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_264) = k7_relat_1('#skF_5',D_264)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_209])).

tff(c_218,plain,(
    ! [D_264] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_264) = k7_relat_1('#skF_5',D_264) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_211])).

tff(c_859,plain,(
    ! [A_371,B_372,C_373,D_374] :
      ( k2_partfun1(u1_struct_0(A_371),u1_struct_0(B_372),C_373,u1_struct_0(D_374)) = k2_tmap_1(A_371,B_372,C_373,D_374)
      | ~ m1_pre_topc(D_374,A_371)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_371),u1_struct_0(B_372))))
      | ~ v1_funct_2(C_373,u1_struct_0(A_371),u1_struct_0(B_372))
      | ~ v1_funct_1(C_373)
      | ~ l1_pre_topc(B_372)
      | ~ v2_pre_topc(B_372)
      | v2_struct_0(B_372)
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371)
      | v2_struct_0(A_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_863,plain,(
    ! [D_374] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_374)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_374)
      | ~ m1_pre_topc(D_374,'#skF_4')
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
    ! [D_374] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_374)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_374)
      | ~ m1_pre_topc(D_374,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_76,c_74,c_64,c_99,c_218,c_863])).

tff(c_875,plain,(
    ! [D_375] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_375)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_375)
      | ~ m1_pre_topc(D_375,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_78,c_869])).

tff(c_122,plain,(
    ! [C_246,A_247,B_248] :
      ( v1_relat_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_122])).

tff(c_149,plain,(
    ! [C_254,A_255,B_256] :
      ( v4_relat_1(C_254,A_255)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
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
    ! [A_419,C_420,B_424,F_421,D_422,E_423] :
      ( r2_funct_2(u1_struct_0(D_422),u1_struct_0(B_424),k3_tmap_1(A_419,B_424,C_420,D_422,F_421),k2_tmap_1(A_419,B_424,E_423,D_422))
      | ~ m1_pre_topc(D_422,C_420)
      | ~ r2_funct_2(u1_struct_0(C_420),u1_struct_0(B_424),F_421,k2_tmap_1(A_419,B_424,E_423,C_420))
      | ~ m1_subset_1(F_421,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_420),u1_struct_0(B_424))))
      | ~ v1_funct_2(F_421,u1_struct_0(C_420),u1_struct_0(B_424))
      | ~ v1_funct_1(F_421)
      | ~ m1_subset_1(E_423,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_419),u1_struct_0(B_424))))
      | ~ v1_funct_2(E_423,u1_struct_0(A_419),u1_struct_0(B_424))
      | ~ v1_funct_1(E_423)
      | ~ m1_pre_topc(D_422,A_419)
      | v2_struct_0(D_422)
      | ~ m1_pre_topc(C_420,A_419)
      | v2_struct_0(C_420)
      | ~ l1_pre_topc(B_424)
      | ~ v2_pre_topc(B_424)
      | v2_struct_0(B_424)
      | ~ l1_pre_topc(A_419)
      | ~ v2_pre_topc(A_419)
      | v2_struct_0(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_1069,plain,(
    ! [D_422,F_421] :
      ( r2_funct_2(u1_struct_0(D_422),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',D_422,F_421),k2_tmap_1('#skF_4','#skF_2','#skF_5',D_422))
      | ~ m1_pre_topc(D_422,'#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),F_421,'#skF_5')
      | ~ m1_subset_1(F_421,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_421,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_421)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_422,'#skF_4')
      | v2_struct_0(D_422)
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_1067])).

tff(c_1073,plain,(
    ! [D_422,F_421] :
      ( r2_funct_2(u1_struct_0(D_422),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',D_422,F_421),k2_tmap_1('#skF_4','#skF_2','#skF_5',D_422))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),F_421,'#skF_5')
      | ~ m1_subset_1(F_421,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_421,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_421)
      | ~ m1_pre_topc(D_422,'#skF_4')
      | v2_struct_0(D_422)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_76,c_74,c_98,c_64,c_99,c_100,c_1069])).

tff(c_1101,plain,(
    ! [D_431,F_432] :
      ( r2_funct_2(u1_struct_0(D_431),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',D_431,F_432),k2_tmap_1('#skF_4','#skF_2','#skF_5',D_431))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),F_432,'#skF_5')
      | ~ m1_subset_1(F_432,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_432,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_432)
      | ~ m1_pre_topc(D_431,'#skF_4')
      | v2_struct_0(D_431) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_78,c_1073])).

tff(c_1111,plain,(
    ! [F_432] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3',F_432),'#skF_6')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),F_432,'#skF_5')
      | ~ m1_subset_1(F_432,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_432,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_432)
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_1101])).

tff(c_1121,plain,(
    ! [F_432] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3',F_432),'#skF_6')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),F_432,'#skF_5')
      | ~ m1_subset_1(F_432,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_432,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_432)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1111])).

tff(c_1150,plain,(
    ! [F_434] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3',F_434),'#skF_6')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),F_434,'#skF_5')
      | ~ m1_subset_1(F_434,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_434,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_434) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1121])).

tff(c_1161,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_1150])).

tff(c_1171,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_234,c_1161])).

tff(c_1173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_775,c_1171])).

tff(c_1175,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_1294,plain,(
    ! [D_453,C_454,A_455,B_456] :
      ( D_453 = C_454
      | ~ r2_funct_2(A_455,B_456,C_454,D_453)
      | ~ m1_subset_1(D_453,k1_zfmisc_1(k2_zfmisc_1(A_455,B_456)))
      | ~ v1_funct_2(D_453,A_455,B_456)
      | ~ v1_funct_1(D_453)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(A_455,B_456)))
      | ~ v1_funct_2(C_454,A_455,B_456)
      | ~ v1_funct_1(C_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1302,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1175,c_1294])).

tff(c_1317,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7') = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1302])).

tff(c_1436,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1317])).

tff(c_1488,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1486,c_1436])).

tff(c_1587,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1584,c_1488])).

tff(c_1590,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_98,c_96,c_1587])).

tff(c_1592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1590])).

tff(c_1594,plain,(
    v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1317])).

tff(c_1895,plain,(
    ! [E_576,C_579,A_575,B_578,D_577] :
      ( m1_subset_1(k3_tmap_1(A_575,B_578,C_579,D_577,E_576),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_577),u1_struct_0(B_578))))
      | ~ m1_subset_1(E_576,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_579),u1_struct_0(B_578))))
      | ~ v1_funct_2(E_576,u1_struct_0(C_579),u1_struct_0(B_578))
      | ~ v1_funct_1(E_576)
      | ~ m1_pre_topc(D_577,A_575)
      | ~ m1_pre_topc(C_579,A_575)
      | ~ l1_pre_topc(B_578)
      | ~ v2_pre_topc(B_578)
      | v2_struct_0(B_578)
      | ~ l1_pre_topc(A_575)
      | ~ v2_pre_topc(A_575)
      | v2_struct_0(A_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1618,plain,(
    ! [C_524,E_525,A_523,D_527,F_526,B_528] :
      ( F_526 = E_525
      | ~ r1_funct_2(A_523,B_528,C_524,D_527,E_525,F_526)
      | ~ m1_subset_1(F_526,k1_zfmisc_1(k2_zfmisc_1(C_524,D_527)))
      | ~ v1_funct_2(F_526,C_524,D_527)
      | ~ v1_funct_1(F_526)
      | ~ m1_subset_1(E_525,k1_zfmisc_1(k2_zfmisc_1(A_523,B_528)))
      | ~ v1_funct_2(E_525,A_523,B_528)
      | ~ v1_funct_1(E_525)
      | v1_xboole_0(D_527)
      | v1_xboole_0(B_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1626,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_102,c_1618])).

tff(c_1644,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99,c_100,c_52,c_50,c_48,c_1626])).

tff(c_1645,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1402,c_1644])).

tff(c_1593,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1317])).

tff(c_1595,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1593])).

tff(c_1647,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_1595])).

tff(c_1910,plain,
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
    inference(resolution,[status(thm)],[c_1895,c_1647])).

tff(c_1940,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_76,c_74,c_98,c_96,c_64,c_99,c_100,c_1910])).

tff(c_1942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_78,c_1940])).

tff(c_1944,plain,(
    m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1593])).

tff(c_22,plain,(
    ! [F_27,A_22,B_23,D_25,C_24] :
      ( r1_funct_2(A_22,B_23,C_24,D_25,F_27,F_27)
      | ~ m1_subset_1(F_27,k1_zfmisc_1(k2_zfmisc_1(C_24,D_25)))
      | ~ v1_funct_2(F_27,C_24,D_25)
      | ~ m1_subset_1(F_27,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(F_27,A_22,B_23)
      | ~ v1_funct_1(F_27)
      | v1_xboole_0(D_25)
      | v1_xboole_0(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1946,plain,(
    ! [A_22,B_23] :
      ( r1_funct_2(A_22,B_23,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'))
      | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),A_22,B_23)
      | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_23) ) ),
    inference(resolution,[status(thm)],[c_1944,c_22])).

tff(c_1966,plain,(
    ! [A_22,B_23] :
      ( r1_funct_2(A_22,B_23,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'))
      | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),A_22,B_23)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1594,c_1946])).

tff(c_1967,plain,(
    ! [A_22,B_23] :
      ( r1_funct_2(A_22,B_23,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'))
      | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),A_22,B_23)
      | v1_xboole_0(B_23) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1402,c_1966])).

tff(c_1989,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1967])).

tff(c_2033,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2030,c_1989])).

tff(c_2306,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2303,c_2033])).

tff(c_2309,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_98,c_96,c_2306])).

tff(c_2311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2309])).

tff(c_2313,plain,(
    v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1967])).

tff(c_1943,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1593])).

tff(c_2319,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2313,c_1943])).

tff(c_2371,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2370,c_2319])).

tff(c_1196,plain,(
    ! [A_439,B_440,C_441,D_442] :
      ( k2_partfun1(A_439,B_440,C_441,D_442) = k7_relat_1(C_441,D_442)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(A_439,B_440)))
      | ~ v1_funct_1(C_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1198,plain,(
    ! [D_442] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_442) = k7_relat_1('#skF_5',D_442)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_1196])).

tff(c_1205,plain,(
    ! [D_442] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_442) = k7_relat_1('#skF_5',D_442) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1198])).

tff(c_2511,plain,(
    ! [A_655,B_656,C_657,D_658] :
      ( k2_partfun1(u1_struct_0(A_655),u1_struct_0(B_656),C_657,u1_struct_0(D_658)) = k2_tmap_1(A_655,B_656,C_657,D_658)
      | ~ m1_pre_topc(D_658,A_655)
      | ~ m1_subset_1(C_657,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_655),u1_struct_0(B_656))))
      | ~ v1_funct_2(C_657,u1_struct_0(A_655),u1_struct_0(B_656))
      | ~ v1_funct_1(C_657)
      | ~ l1_pre_topc(B_656)
      | ~ v2_pre_topc(B_656)
      | v2_struct_0(B_656)
      | ~ l1_pre_topc(A_655)
      | ~ v2_pre_topc(A_655)
      | v2_struct_0(A_655) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2515,plain,(
    ! [D_658] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_658)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_658)
      | ~ m1_pre_topc(D_658,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_100,c_2511])).

tff(c_2521,plain,(
    ! [D_658] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_658)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_658)
      | ~ m1_pre_topc(D_658,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_76,c_74,c_64,c_99,c_1205,c_2515])).

tff(c_2528,plain,(
    ! [D_660] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_660)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_660)
      | ~ m1_pre_topc(D_660,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_78,c_2521])).

tff(c_2534,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2528,c_167])).

tff(c_2543,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_2534])).

tff(c_2691,plain,(
    ! [D_687,E_688,C_685,B_689,F_686,A_684] :
      ( r2_funct_2(u1_struct_0(D_687),u1_struct_0(B_689),k3_tmap_1(A_684,B_689,C_685,D_687,F_686),k2_tmap_1(A_684,B_689,E_688,D_687))
      | ~ m1_pre_topc(D_687,C_685)
      | ~ r2_funct_2(u1_struct_0(C_685),u1_struct_0(B_689),F_686,k2_tmap_1(A_684,B_689,E_688,C_685))
      | ~ m1_subset_1(F_686,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_685),u1_struct_0(B_689))))
      | ~ v1_funct_2(F_686,u1_struct_0(C_685),u1_struct_0(B_689))
      | ~ v1_funct_1(F_686)
      | ~ m1_subset_1(E_688,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_684),u1_struct_0(B_689))))
      | ~ v1_funct_2(E_688,u1_struct_0(A_684),u1_struct_0(B_689))
      | ~ v1_funct_1(E_688)
      | ~ m1_pre_topc(D_687,A_684)
      | v2_struct_0(D_687)
      | ~ m1_pre_topc(C_685,A_684)
      | v2_struct_0(C_685)
      | ~ l1_pre_topc(B_689)
      | ~ v2_pre_topc(B_689)
      | v2_struct_0(B_689)
      | ~ l1_pre_topc(A_684)
      | ~ v2_pre_topc(A_684)
      | v2_struct_0(A_684) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_2693,plain,(
    ! [D_687,F_686] :
      ( r2_funct_2(u1_struct_0(D_687),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',D_687,F_686),k2_tmap_1('#skF_4','#skF_2','#skF_5',D_687))
      | ~ m1_pre_topc(D_687,'#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),F_686,'#skF_5')
      | ~ m1_subset_1(F_686,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_686,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_686)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_687,'#skF_4')
      | v2_struct_0(D_687)
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2543,c_2691])).

tff(c_2695,plain,(
    ! [D_687,F_686] :
      ( r2_funct_2(u1_struct_0(D_687),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',D_687,F_686),k2_tmap_1('#skF_4','#skF_2','#skF_5',D_687))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),F_686,'#skF_5')
      | ~ m1_subset_1(F_686,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_686,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_686)
      | ~ m1_pre_topc(D_687,'#skF_4')
      | v2_struct_0(D_687)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95,c_76,c_74,c_98,c_64,c_99,c_100,c_2693])).

tff(c_2783,plain,(
    ! [D_712,F_713] :
      ( r2_funct_2(u1_struct_0(D_712),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',D_712,F_713),k2_tmap_1('#skF_4','#skF_2','#skF_5',D_712))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),F_713,'#skF_5')
      | ~ m1_subset_1(F_713,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_713,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_713)
      | ~ m1_pre_topc(D_712,'#skF_4')
      | v2_struct_0(D_712) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_78,c_2695])).

tff(c_2793,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2371,c_2783])).

tff(c_2803,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_99,c_100,c_1250,c_2793])).

tff(c_2804,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2803])).

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

tff(c_2808,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2804,c_14])).

tff(c_2815,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2808])).

tff(c_2833,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2815])).

tff(c_2836,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1336,c_2833])).

tff(c_2840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_2836])).

tff(c_2842,plain,(
    v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2815])).

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

tff(c_2841,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2815])).

tff(c_2910,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2841])).

tff(c_2913,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_2910])).

tff(c_2917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_1293,c_64,c_99,c_100,c_1283,c_2913])).

tff(c_2919,plain,(
    m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_2841])).

tff(c_38,plain,(
    ! [A_47,E_51,D_50,C_49,B_48] :
      ( v1_funct_1(k3_tmap_1(A_47,B_48,C_49,D_50,E_51))
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_49),u1_struct_0(B_48))))
      | ~ v1_funct_2(E_51,u1_struct_0(C_49),u1_struct_0(B_48))
      | ~ v1_funct_1(E_51)
      | ~ m1_pre_topc(D_50,A_47)
      | ~ m1_pre_topc(C_49,A_47)
      | ~ l1_pre_topc(B_48)
      | ~ v2_pre_topc(B_48)
      | v2_struct_0(B_48)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2937,plain,(
    ! [A_47,D_50] :
      ( v1_funct_1(k3_tmap_1(A_47,'#skF_2','#skF_3',D_50,k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')))
      | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc(D_50,A_47)
      | ~ m1_pre_topc('#skF_3',A_47)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_2919,c_38])).

tff(c_2990,plain,(
    ! [A_47,D_50] :
      ( v1_funct_1(k3_tmap_1(A_47,'#skF_2','#skF_3',D_50,k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')))
      | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_50,A_47)
      | ~ m1_pre_topc('#skF_3',A_47)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_2842,c_2937])).

tff(c_2991,plain,(
    ! [A_47,D_50] :
      ( v1_funct_1(k3_tmap_1(A_47,'#skF_2','#skF_3',D_50,k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')))
      | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_50,A_47)
      | ~ m1_pre_topc('#skF_3',A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2990])).

tff(c_3051,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2991])).

tff(c_3054,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1349,c_3051])).

tff(c_3058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_3054])).

tff(c_3060,plain,(
    v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2991])).

tff(c_2918,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2841])).

tff(c_3068,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3060,c_2918])).

tff(c_1174,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_3078,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3068,c_1174])).

tff(c_3089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1256,c_3078])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:15:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.16/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.18  
% 6.16/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.18  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.16/2.18  
% 6.16/2.18  %Foreground sorts:
% 6.16/2.18  
% 6.16/2.18  
% 6.16/2.18  %Background operators:
% 6.16/2.18  
% 6.16/2.18  
% 6.16/2.18  %Foreground operators:
% 6.16/2.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.16/2.18  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 6.16/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.16/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.16/2.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.16/2.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.16/2.18  tff('#skF_7', type, '#skF_7': $i).
% 6.16/2.18  tff('#skF_5', type, '#skF_5': $i).
% 6.16/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.16/2.18  tff('#skF_6', type, '#skF_6': $i).
% 6.16/2.18  tff('#skF_2', type, '#skF_2': $i).
% 6.16/2.18  tff('#skF_3', type, '#skF_3': $i).
% 6.16/2.18  tff('#skF_1', type, '#skF_1': $i).
% 6.16/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.16/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.16/2.19  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.16/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.16/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.16/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.16/2.19  tff('#skF_4', type, '#skF_4': $i).
% 6.16/2.19  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 6.16/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.16/2.19  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.16/2.19  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.16/2.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.16/2.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.16/2.19  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.16/2.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.16/2.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.16/2.19  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 6.16/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.16/2.19  
% 6.55/2.23  tff(f_295, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 6.55/2.23  tff(f_63, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 6.55/2.23  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.55/2.23  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.55/2.23  tff(f_149, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 6.55/2.23  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 6.55/2.23  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.55/2.23  tff(f_179, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 6.55/2.23  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.55/2.23  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.55/2.23  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.55/2.23  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.55/2.23  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 6.55/2.23  tff(f_226, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), F, k2_tmap_1(A, B, E, C)) & m1_pre_topc(D, C)) => r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, C, D, F), k2_tmap_1(A, B, E, D))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tmap_1)).
% 6.55/2.23  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_56, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_1241, plain, (![A_446, B_447, D_448]: (r2_funct_2(A_446, B_447, D_448, D_448) | ~m1_subset_1(D_448, k1_zfmisc_1(k2_zfmisc_1(A_446, B_447))) | ~v1_funct_2(D_448, A_446, B_447) | ~v1_funct_1(D_448))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.55/2.23  tff(c_1247, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_1241])).
% 6.55/2.23  tff(c_1256, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1247])).
% 6.55/2.23  tff(c_46, plain, ('#skF_1'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_80, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_95, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_80])).
% 6.55/2.23  tff(c_70, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_96, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_70])).
% 6.55/2.23  tff(c_108, plain, (![B_243, A_244]: (l1_pre_topc(B_243) | ~m1_pre_topc(B_243, A_244) | ~l1_pre_topc(A_244))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.55/2.23  tff(c_114, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_108])).
% 6.55/2.23  tff(c_120, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_114])).
% 6.55/2.23  tff(c_16, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.55/2.23  tff(c_1257, plain, (![A_449, B_450, C_451, D_452]: (v1_funct_1(k2_tmap_1(A_449, B_450, C_451, D_452)) | ~l1_struct_0(D_452) | ~m1_subset_1(C_451, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_449), u1_struct_0(B_450)))) | ~v1_funct_2(C_451, u1_struct_0(A_449), u1_struct_0(B_450)) | ~v1_funct_1(C_451) | ~l1_struct_0(B_450) | ~l1_struct_0(A_449))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.55/2.23  tff(c_1263, plain, (![D_452]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_452)) | ~l1_struct_0(D_452) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_1257])).
% 6.55/2.23  tff(c_1272, plain, (![D_452]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_452)) | ~l1_struct_0(D_452) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1263])).
% 6.55/2.23  tff(c_1273, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1272])).
% 6.55/2.23  tff(c_1277, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_1273])).
% 6.55/2.23  tff(c_1281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_1277])).
% 6.55/2.23  tff(c_1283, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1272])).
% 6.55/2.23  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_1282, plain, (![D_452]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_452)) | ~l1_struct_0(D_452))), inference(splitRight, [status(thm)], [c_1272])).
% 6.55/2.23  tff(c_1284, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1282])).
% 6.55/2.23  tff(c_1287, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1284])).
% 6.55/2.23  tff(c_1291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1287])).
% 6.55/2.23  tff(c_1293, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1282])).
% 6.55/2.23  tff(c_52, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_50, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_1261, plain, (![D_452]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_452)) | ~l1_struct_0(D_452) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_1257])).
% 6.55/2.23  tff(c_1269, plain, (![D_452]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_452)) | ~l1_struct_0(D_452) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1261])).
% 6.55/2.23  tff(c_1320, plain, (![D_452]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_452)) | ~l1_struct_0(D_452) | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_1269])).
% 6.55/2.23  tff(c_1321, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1320])).
% 6.55/2.23  tff(c_1324, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_1321])).
% 6.55/2.23  tff(c_1328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_1324])).
% 6.55/2.23  tff(c_1330, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1320])).
% 6.55/2.23  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_62, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_99, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_62])).
% 6.55/2.23  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_100, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_60])).
% 6.55/2.23  tff(c_1340, plain, (![A_459, B_460, C_461, D_462]: (v1_funct_2(k2_tmap_1(A_459, B_460, C_461, D_462), u1_struct_0(D_462), u1_struct_0(B_460)) | ~l1_struct_0(D_462) | ~m1_subset_1(C_461, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_459), u1_struct_0(B_460)))) | ~v1_funct_2(C_461, u1_struct_0(A_459), u1_struct_0(B_460)) | ~v1_funct_1(C_461) | ~l1_struct_0(B_460) | ~l1_struct_0(A_459))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.55/2.23  tff(c_1342, plain, (![D_462]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_462), u1_struct_0(D_462), u1_struct_0('#skF_2')) | ~l1_struct_0(D_462) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_1340])).
% 6.55/2.23  tff(c_1349, plain, (![D_462]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_462), u1_struct_0(D_462), u1_struct_0('#skF_2')) | ~l1_struct_0(D_462))), inference(demodulation, [status(thm), theory('equality')], [c_1330, c_1293, c_64, c_99, c_1342])).
% 6.55/2.23  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_1259, plain, (![D_452]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_452)) | ~l1_struct_0(D_452) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_1257])).
% 6.55/2.23  tff(c_1266, plain, (![D_452]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_452)) | ~l1_struct_0(D_452) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_1259])).
% 6.55/2.23  tff(c_1332, plain, (![D_452]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_452)) | ~l1_struct_0(D_452) | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_1266])).
% 6.55/2.23  tff(c_1333, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1332])).
% 6.55/2.23  tff(c_1335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1330, c_1333])).
% 6.55/2.23  tff(c_1336, plain, (![D_452]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_452)) | ~l1_struct_0(D_452))), inference(splitRight, [status(thm)], [c_1332])).
% 6.55/2.23  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_1243, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_1241])).
% 6.55/2.23  tff(c_1250, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_1243])).
% 6.55/2.23  tff(c_1376, plain, (![B_473, F_471, C_470, D_472, A_469]: (r1_funct_2(A_469, B_473, C_470, D_472, F_471, F_471) | ~m1_subset_1(F_471, k1_zfmisc_1(k2_zfmisc_1(C_470, D_472))) | ~v1_funct_2(F_471, C_470, D_472) | ~m1_subset_1(F_471, k1_zfmisc_1(k2_zfmisc_1(A_469, B_473))) | ~v1_funct_2(F_471, A_469, B_473) | ~v1_funct_1(F_471) | v1_xboole_0(D_472) | v1_xboole_0(B_473))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.23  tff(c_1378, plain, (![A_469, B_473]: (r1_funct_2(A_469, B_473, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_469, B_473))) | ~v1_funct_2('#skF_5', A_469, B_473) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_473))), inference(resolution, [status(thm)], [c_100, c_1376])).
% 6.55/2.23  tff(c_1385, plain, (![A_469, B_473]: (r1_funct_2(A_469, B_473, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_469, B_473))) | ~v1_funct_2('#skF_5', A_469, B_473) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_473))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_1378])).
% 6.55/2.23  tff(c_1392, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1385])).
% 6.55/2.23  tff(c_20, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.55/2.23  tff(c_1395, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1392, c_20])).
% 6.55/2.23  tff(c_1398, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_1395])).
% 6.55/2.23  tff(c_1400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1398])).
% 6.55/2.23  tff(c_1402, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1385])).
% 6.55/2.23  tff(c_44, plain, (r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_102, plain, (r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 6.55/2.23  tff(c_2343, plain, (![A_621, C_622, B_626, D_625, E_623, F_624]: (F_624=E_623 | ~r1_funct_2(A_621, B_626, C_622, D_625, E_623, F_624) | ~m1_subset_1(F_624, k1_zfmisc_1(k2_zfmisc_1(C_622, D_625))) | ~v1_funct_2(F_624, C_622, D_625) | ~v1_funct_1(F_624) | ~m1_subset_1(E_623, k1_zfmisc_1(k2_zfmisc_1(A_621, B_626))) | ~v1_funct_2(E_623, A_621, B_626) | ~v1_funct_1(E_623) | v1_xboole_0(D_625) | v1_xboole_0(B_626))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.23  tff(c_2351, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_102, c_2343])).
% 6.55/2.23  tff(c_2369, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_100, c_52, c_50, c_48, c_2351])).
% 6.55/2.23  tff(c_2370, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1402, c_2369])).
% 6.55/2.23  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_82, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_94, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_82])).
% 6.55/2.23  tff(c_66, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_98, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_66])).
% 6.55/2.23  tff(c_2274, plain, (![B_615, A_612, D_614, E_613, C_616]: (v1_funct_2(k3_tmap_1(A_612, B_615, C_616, D_614, E_613), u1_struct_0(D_614), u1_struct_0(B_615)) | ~m1_subset_1(E_613, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_616), u1_struct_0(B_615)))) | ~v1_funct_2(E_613, u1_struct_0(C_616), u1_struct_0(B_615)) | ~v1_funct_1(E_613) | ~m1_pre_topc(D_614, A_612) | ~m1_pre_topc(C_616, A_612) | ~l1_pre_topc(B_615) | ~v2_pre_topc(B_615) | v2_struct_0(B_615) | ~l1_pre_topc(A_612) | ~v2_pre_topc(A_612) | v2_struct_0(A_612))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.55/2.23  tff(c_2280, plain, (![A_612, D_614]: (v1_funct_2(k3_tmap_1(A_612, '#skF_2', '#skF_4', D_614, '#skF_5'), u1_struct_0(D_614), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_614, A_612) | ~m1_pre_topc('#skF_4', A_612) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_612) | ~v2_pre_topc(A_612) | v2_struct_0(A_612))), inference(resolution, [status(thm)], [c_100, c_2274])).
% 6.55/2.23  tff(c_2290, plain, (![A_612, D_614]: (v1_funct_2(k3_tmap_1(A_612, '#skF_2', '#skF_4', D_614, '#skF_5'), u1_struct_0(D_614), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_614, A_612) | ~m1_pre_topc('#skF_4', A_612) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_612) | ~v2_pre_topc(A_612) | v2_struct_0(A_612))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_99, c_2280])).
% 6.55/2.23  tff(c_2303, plain, (![A_619, D_620]: (v1_funct_2(k3_tmap_1(A_619, '#skF_2', '#skF_4', D_620, '#skF_5'), u1_struct_0(D_620), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_620, A_619) | ~m1_pre_topc('#skF_4', A_619) | ~l1_pre_topc(A_619) | ~v2_pre_topc(A_619) | v2_struct_0(A_619))), inference(negUnitSimplification, [status(thm)], [c_78, c_2290])).
% 6.55/2.23  tff(c_2003, plain, (![E_583, C_582, A_581, D_585, F_584, B_586]: (F_584=E_583 | ~r1_funct_2(A_581, B_586, C_582, D_585, E_583, F_584) | ~m1_subset_1(F_584, k1_zfmisc_1(k2_zfmisc_1(C_582, D_585))) | ~v1_funct_2(F_584, C_582, D_585) | ~v1_funct_1(F_584) | ~m1_subset_1(E_583, k1_zfmisc_1(k2_zfmisc_1(A_581, B_586))) | ~v1_funct_2(E_583, A_581, B_586) | ~v1_funct_1(E_583) | v1_xboole_0(D_585) | v1_xboole_0(B_586))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.23  tff(c_2011, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_102, c_2003])).
% 6.55/2.23  tff(c_2029, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_100, c_52, c_50, c_48, c_2011])).
% 6.55/2.23  tff(c_2030, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1402, c_2029])).
% 6.55/2.23  tff(c_1563, plain, (![B_511, E_509, D_510, A_508, C_512]: (v1_funct_1(k3_tmap_1(A_508, B_511, C_512, D_510, E_509)) | ~m1_subset_1(E_509, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_512), u1_struct_0(B_511)))) | ~v1_funct_2(E_509, u1_struct_0(C_512), u1_struct_0(B_511)) | ~v1_funct_1(E_509) | ~m1_pre_topc(D_510, A_508) | ~m1_pre_topc(C_512, A_508) | ~l1_pre_topc(B_511) | ~v2_pre_topc(B_511) | v2_struct_0(B_511) | ~l1_pre_topc(A_508) | ~v2_pre_topc(A_508) | v2_struct_0(A_508))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.55/2.23  tff(c_1567, plain, (![A_508, D_510]: (v1_funct_1(k3_tmap_1(A_508, '#skF_2', '#skF_4', D_510, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_510, A_508) | ~m1_pre_topc('#skF_4', A_508) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_508) | ~v2_pre_topc(A_508) | v2_struct_0(A_508))), inference(resolution, [status(thm)], [c_100, c_1563])).
% 6.55/2.23  tff(c_1573, plain, (![A_508, D_510]: (v1_funct_1(k3_tmap_1(A_508, '#skF_2', '#skF_4', D_510, '#skF_5')) | ~m1_pre_topc(D_510, A_508) | ~m1_pre_topc('#skF_4', A_508) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_508) | ~v2_pre_topc(A_508) | v2_struct_0(A_508))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_99, c_1567])).
% 6.55/2.23  tff(c_1584, plain, (![A_514, D_515]: (v1_funct_1(k3_tmap_1(A_514, '#skF_2', '#skF_4', D_515, '#skF_5')) | ~m1_pre_topc(D_515, A_514) | ~m1_pre_topc('#skF_4', A_514) | ~l1_pre_topc(A_514) | ~v2_pre_topc(A_514) | v2_struct_0(A_514))), inference(negUnitSimplification, [status(thm)], [c_78, c_1573])).
% 6.55/2.23  tff(c_1459, plain, (![E_493, A_491, D_495, F_494, C_492, B_496]: (F_494=E_493 | ~r1_funct_2(A_491, B_496, C_492, D_495, E_493, F_494) | ~m1_subset_1(F_494, k1_zfmisc_1(k2_zfmisc_1(C_492, D_495))) | ~v1_funct_2(F_494, C_492, D_495) | ~v1_funct_1(F_494) | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1(A_491, B_496))) | ~v1_funct_2(E_493, A_491, B_496) | ~v1_funct_1(E_493) | v1_xboole_0(D_495) | v1_xboole_0(B_496))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.23  tff(c_1467, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_102, c_1459])).
% 6.55/2.23  tff(c_1485, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_100, c_52, c_50, c_48, c_1467])).
% 6.55/2.23  tff(c_1486, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1402, c_1485])).
% 6.55/2.23  tff(c_285, plain, (![A_273, B_274, C_275, D_276]: (v1_funct_1(k2_tmap_1(A_273, B_274, C_275, D_276)) | ~l1_struct_0(D_276) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_273), u1_struct_0(B_274)))) | ~v1_funct_2(C_275, u1_struct_0(A_273), u1_struct_0(B_274)) | ~v1_funct_1(C_275) | ~l1_struct_0(B_274) | ~l1_struct_0(A_273))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.55/2.23  tff(c_287, plain, (![D_276]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_276)) | ~l1_struct_0(D_276) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_285])).
% 6.55/2.23  tff(c_294, plain, (![D_276]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_276)) | ~l1_struct_0(D_276) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_287])).
% 6.55/2.23  tff(c_325, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_294])).
% 6.55/2.23  tff(c_328, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_325])).
% 6.55/2.23  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_328])).
% 6.55/2.23  tff(c_334, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_294])).
% 6.55/2.23  tff(c_289, plain, (![D_276]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_276)) | ~l1_struct_0(D_276) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_285])).
% 6.55/2.23  tff(c_297, plain, (![D_276]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_276)) | ~l1_struct_0(D_276) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_289])).
% 6.55/2.23  tff(c_336, plain, (![D_276]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_276)) | ~l1_struct_0(D_276) | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_297])).
% 6.55/2.23  tff(c_337, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_336])).
% 6.55/2.23  tff(c_340, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_337])).
% 6.55/2.23  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_340])).
% 6.55/2.23  tff(c_346, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_336])).
% 6.55/2.23  tff(c_594, plain, (![F_322, A_320, C_321, D_323, B_324]: (r1_funct_2(A_320, B_324, C_321, D_323, F_322, F_322) | ~m1_subset_1(F_322, k1_zfmisc_1(k2_zfmisc_1(C_321, D_323))) | ~v1_funct_2(F_322, C_321, D_323) | ~m1_subset_1(F_322, k1_zfmisc_1(k2_zfmisc_1(A_320, B_324))) | ~v1_funct_2(F_322, A_320, B_324) | ~v1_funct_1(F_322) | v1_xboole_0(D_323) | v1_xboole_0(B_324))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.23  tff(c_598, plain, (![A_320, B_324]: (r1_funct_2(A_320, B_324, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_7', '#skF_7') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_320, B_324))) | ~v1_funct_2('#skF_7', A_320, B_324) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_324))), inference(resolution, [status(thm)], [c_48, c_594])).
% 6.55/2.23  tff(c_606, plain, (![A_320, B_324]: (r1_funct_2(A_320, B_324, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_7', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_320, B_324))) | ~v1_funct_2('#skF_7', A_320, B_324) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_324))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_598])).
% 6.55/2.23  tff(c_618, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_606])).
% 6.55/2.23  tff(c_621, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_618, c_20])).
% 6.55/2.23  tff(c_624, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_621])).
% 6.55/2.23  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_624])).
% 6.55/2.23  tff(c_628, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_606])).
% 6.55/2.23  tff(c_740, plain, (![F_359, C_357, B_361, A_356, E_358, D_360]: (F_359=E_358 | ~r1_funct_2(A_356, B_361, C_357, D_360, E_358, F_359) | ~m1_subset_1(F_359, k1_zfmisc_1(k2_zfmisc_1(C_357, D_360))) | ~v1_funct_2(F_359, C_357, D_360) | ~v1_funct_1(F_359) | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(A_356, B_361))) | ~v1_funct_2(E_358, A_356, B_361) | ~v1_funct_1(E_358) | v1_xboole_0(D_360) | v1_xboole_0(B_361))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.23  tff(c_748, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_102, c_740])).
% 6.55/2.23  tff(c_766, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_100, c_52, c_50, c_48, c_748])).
% 6.55/2.23  tff(c_767, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_628, c_766])).
% 6.55/2.23  tff(c_86, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_101, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_86])).
% 6.55/2.23  tff(c_188, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_101])).
% 6.55/2.23  tff(c_775, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_767, c_188])).
% 6.55/2.23  tff(c_225, plain, (![A_265, B_266, D_267]: (r2_funct_2(A_265, B_266, D_267, D_267) | ~m1_subset_1(D_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))) | ~v1_funct_2(D_267, A_265, B_266) | ~v1_funct_1(D_267))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.55/2.23  tff(c_227, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_225])).
% 6.55/2.23  tff(c_234, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_227])).
% 6.55/2.23  tff(c_291, plain, (![D_276]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_276)) | ~l1_struct_0(D_276) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_285])).
% 6.55/2.23  tff(c_300, plain, (![D_276]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_276)) | ~l1_struct_0(D_276) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_291])).
% 6.55/2.23  tff(c_352, plain, (![D_276]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_276)) | ~l1_struct_0(D_276) | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_300])).
% 6.55/2.23  tff(c_353, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_352])).
% 6.55/2.23  tff(c_372, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_353])).
% 6.55/2.23  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_372])).
% 6.55/2.23  tff(c_378, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_352])).
% 6.55/2.23  tff(c_520, plain, (![A_311, B_312, C_313, D_314]: (v1_funct_2(k2_tmap_1(A_311, B_312, C_313, D_314), u1_struct_0(D_314), u1_struct_0(B_312)) | ~l1_struct_0(D_314) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_311), u1_struct_0(B_312)))) | ~v1_funct_2(C_313, u1_struct_0(A_311), u1_struct_0(B_312)) | ~v1_funct_1(C_313) | ~l1_struct_0(B_312) | ~l1_struct_0(A_311))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.55/2.23  tff(c_524, plain, (![D_314]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_314), u1_struct_0(D_314), u1_struct_0('#skF_2')) | ~l1_struct_0(D_314) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_520])).
% 6.55/2.23  tff(c_541, plain, (![D_315]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_315), u1_struct_0(D_315), u1_struct_0('#skF_2')) | ~l1_struct_0(D_315))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_346, c_64, c_99, c_524])).
% 6.55/2.23  tff(c_442, plain, (![A_306, B_307, C_308, D_309]: (m1_subset_1(k2_tmap_1(A_306, B_307, C_308, D_309), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_309), u1_struct_0(B_307)))) | ~l1_struct_0(D_309) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_306), u1_struct_0(B_307)))) | ~v1_funct_2(C_308, u1_struct_0(A_306), u1_struct_0(B_307)) | ~v1_funct_1(C_308) | ~l1_struct_0(B_307) | ~l1_struct_0(A_306))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.55/2.23  tff(c_333, plain, (![D_276]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_276)) | ~l1_struct_0(D_276))), inference(splitRight, [status(thm)], [c_294])).
% 6.55/2.23  tff(c_349, plain, (![D_276]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_276)) | ~l1_struct_0(D_276))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_333])).
% 6.55/2.23  tff(c_92, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_295])).
% 6.55/2.23  tff(c_97, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_92])).
% 6.55/2.23  tff(c_241, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_188, c_97])).
% 6.55/2.23  tff(c_301, plain, (![D_277, C_278, A_279, B_280]: (D_277=C_278 | ~r2_funct_2(A_279, B_280, C_278, D_277) | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))) | ~v1_funct_2(D_277, A_279, B_280) | ~v1_funct_1(D_277) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))) | ~v1_funct_2(C_278, A_279, B_280) | ~v1_funct_1(C_278))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.55/2.23  tff(c_303, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_241, c_301])).
% 6.55/2.23  tff(c_312, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_303])).
% 6.55/2.23  tff(c_380, plain, (~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_312])).
% 6.55/2.23  tff(c_383, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_349, c_380])).
% 6.55/2.23  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_378, c_383])).
% 6.55/2.23  tff(c_388, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_312])).
% 6.55/2.23  tff(c_390, plain, (~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_388])).
% 6.55/2.23  tff(c_449, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_442, c_390])).
% 6.55/2.23  tff(c_470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_334, c_346, c_64, c_99, c_100, c_378, c_449])).
% 6.55/2.23  tff(c_471, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_388])).
% 6.55/2.23  tff(c_506, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_471])).
% 6.55/2.23  tff(c_544, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_541, c_506])).
% 6.55/2.23  tff(c_548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_378, c_544])).
% 6.55/2.23  tff(c_549, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_471])).
% 6.55/2.23  tff(c_209, plain, (![A_261, B_262, C_263, D_264]: (k2_partfun1(A_261, B_262, C_263, D_264)=k7_relat_1(C_263, D_264) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_1(C_263))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.55/2.23  tff(c_211, plain, (![D_264]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_264)=k7_relat_1('#skF_5', D_264) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_100, c_209])).
% 6.55/2.23  tff(c_218, plain, (![D_264]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_264)=k7_relat_1('#skF_5', D_264))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_211])).
% 6.55/2.23  tff(c_859, plain, (![A_371, B_372, C_373, D_374]: (k2_partfun1(u1_struct_0(A_371), u1_struct_0(B_372), C_373, u1_struct_0(D_374))=k2_tmap_1(A_371, B_372, C_373, D_374) | ~m1_pre_topc(D_374, A_371) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_371), u1_struct_0(B_372)))) | ~v1_funct_2(C_373, u1_struct_0(A_371), u1_struct_0(B_372)) | ~v1_funct_1(C_373) | ~l1_pre_topc(B_372) | ~v2_pre_topc(B_372) | v2_struct_0(B_372) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371) | v2_struct_0(A_371))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.55/2.23  tff(c_863, plain, (![D_374]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_374))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_374) | ~m1_pre_topc(D_374, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_859])).
% 6.55/2.23  tff(c_869, plain, (![D_374]: (k7_relat_1('#skF_5', u1_struct_0(D_374))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_374) | ~m1_pre_topc(D_374, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_76, c_74, c_64, c_99, c_218, c_863])).
% 6.55/2.23  tff(c_875, plain, (![D_375]: (k7_relat_1('#skF_5', u1_struct_0(D_375))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_375) | ~m1_pre_topc(D_375, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_78, c_869])).
% 6.55/2.23  tff(c_122, plain, (![C_246, A_247, B_248]: (v1_relat_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.55/2.23  tff(c_132, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_122])).
% 6.55/2.23  tff(c_149, plain, (![C_254, A_255, B_256]: (v4_relat_1(C_254, A_255) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.55/2.23  tff(c_159, plain, (v4_relat_1('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_149])).
% 6.55/2.23  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.55/2.23  tff(c_164, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_159, c_2])).
% 6.55/2.23  tff(c_167, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_164])).
% 6.55/2.23  tff(c_881, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_875, c_167])).
% 6.55/2.23  tff(c_890, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_881])).
% 6.55/2.23  tff(c_1067, plain, (![A_419, C_420, B_424, F_421, D_422, E_423]: (r2_funct_2(u1_struct_0(D_422), u1_struct_0(B_424), k3_tmap_1(A_419, B_424, C_420, D_422, F_421), k2_tmap_1(A_419, B_424, E_423, D_422)) | ~m1_pre_topc(D_422, C_420) | ~r2_funct_2(u1_struct_0(C_420), u1_struct_0(B_424), F_421, k2_tmap_1(A_419, B_424, E_423, C_420)) | ~m1_subset_1(F_421, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_420), u1_struct_0(B_424)))) | ~v1_funct_2(F_421, u1_struct_0(C_420), u1_struct_0(B_424)) | ~v1_funct_1(F_421) | ~m1_subset_1(E_423, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_419), u1_struct_0(B_424)))) | ~v1_funct_2(E_423, u1_struct_0(A_419), u1_struct_0(B_424)) | ~v1_funct_1(E_423) | ~m1_pre_topc(D_422, A_419) | v2_struct_0(D_422) | ~m1_pre_topc(C_420, A_419) | v2_struct_0(C_420) | ~l1_pre_topc(B_424) | ~v2_pre_topc(B_424) | v2_struct_0(B_424) | ~l1_pre_topc(A_419) | ~v2_pre_topc(A_419) | v2_struct_0(A_419))), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.55/2.23  tff(c_1069, plain, (![D_422, F_421]: (r2_funct_2(u1_struct_0(D_422), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', D_422, F_421), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_422)) | ~m1_pre_topc(D_422, '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), F_421, '#skF_5') | ~m1_subset_1(F_421, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_421, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_421) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_422, '#skF_4') | v2_struct_0(D_422) | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_890, c_1067])).
% 6.55/2.23  tff(c_1073, plain, (![D_422, F_421]: (r2_funct_2(u1_struct_0(D_422), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', D_422, F_421), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_422)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), F_421, '#skF_5') | ~m1_subset_1(F_421, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_421, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_421) | ~m1_pre_topc(D_422, '#skF_4') | v2_struct_0(D_422) | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_76, c_74, c_98, c_64, c_99, c_100, c_1069])).
% 6.55/2.23  tff(c_1101, plain, (![D_431, F_432]: (r2_funct_2(u1_struct_0(D_431), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', D_431, F_432), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_431)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), F_432, '#skF_5') | ~m1_subset_1(F_432, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_432, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_432) | ~m1_pre_topc(D_431, '#skF_4') | v2_struct_0(D_431))), inference(negUnitSimplification, [status(thm)], [c_68, c_78, c_1073])).
% 6.55/2.23  tff(c_1111, plain, (![F_432]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', F_432), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), F_432, '#skF_5') | ~m1_subset_1(F_432, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_432, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_432) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_549, c_1101])).
% 6.55/2.23  tff(c_1121, plain, (![F_432]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', F_432), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), F_432, '#skF_5') | ~m1_subset_1(F_432, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_432, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_432) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1111])).
% 6.55/2.23  tff(c_1150, plain, (![F_434]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', F_434), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), F_434, '#skF_5') | ~m1_subset_1(F_434, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_434, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_434))), inference(negUnitSimplification, [status(thm)], [c_72, c_1121])).
% 6.55/2.23  tff(c_1161, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_1150])).
% 6.55/2.23  tff(c_1171, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_234, c_1161])).
% 6.55/2.23  tff(c_1173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_775, c_1171])).
% 6.55/2.23  tff(c_1175, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_101])).
% 6.55/2.23  tff(c_1294, plain, (![D_453, C_454, A_455, B_456]: (D_453=C_454 | ~r2_funct_2(A_455, B_456, C_454, D_453) | ~m1_subset_1(D_453, k1_zfmisc_1(k2_zfmisc_1(A_455, B_456))) | ~v1_funct_2(D_453, A_455, B_456) | ~v1_funct_1(D_453) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(A_455, B_456))) | ~v1_funct_2(C_454, A_455, B_456) | ~v1_funct_1(C_454))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.55/2.23  tff(c_1302, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'))), inference(resolution, [status(thm)], [c_1175, c_1294])).
% 6.55/2.23  tff(c_1317, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1302])).
% 6.55/2.23  tff(c_1436, plain, (~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'))), inference(splitLeft, [status(thm)], [c_1317])).
% 6.55/2.23  tff(c_1488, plain, (~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1486, c_1436])).
% 6.55/2.23  tff(c_1587, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1584, c_1488])).
% 6.55/2.23  tff(c_1590, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_98, c_96, c_1587])).
% 6.55/2.23  tff(c_1592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1590])).
% 6.55/2.23  tff(c_1594, plain, (v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'))), inference(splitRight, [status(thm)], [c_1317])).
% 6.55/2.23  tff(c_1895, plain, (![E_576, C_579, A_575, B_578, D_577]: (m1_subset_1(k3_tmap_1(A_575, B_578, C_579, D_577, E_576), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_577), u1_struct_0(B_578)))) | ~m1_subset_1(E_576, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_579), u1_struct_0(B_578)))) | ~v1_funct_2(E_576, u1_struct_0(C_579), u1_struct_0(B_578)) | ~v1_funct_1(E_576) | ~m1_pre_topc(D_577, A_575) | ~m1_pre_topc(C_579, A_575) | ~l1_pre_topc(B_578) | ~v2_pre_topc(B_578) | v2_struct_0(B_578) | ~l1_pre_topc(A_575) | ~v2_pre_topc(A_575) | v2_struct_0(A_575))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.55/2.23  tff(c_1618, plain, (![C_524, E_525, A_523, D_527, F_526, B_528]: (F_526=E_525 | ~r1_funct_2(A_523, B_528, C_524, D_527, E_525, F_526) | ~m1_subset_1(F_526, k1_zfmisc_1(k2_zfmisc_1(C_524, D_527))) | ~v1_funct_2(F_526, C_524, D_527) | ~v1_funct_1(F_526) | ~m1_subset_1(E_525, k1_zfmisc_1(k2_zfmisc_1(A_523, B_528))) | ~v1_funct_2(E_525, A_523, B_528) | ~v1_funct_1(E_525) | v1_xboole_0(D_527) | v1_xboole_0(B_528))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.23  tff(c_1626, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_102, c_1618])).
% 6.55/2.23  tff(c_1644, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99, c_100, c_52, c_50, c_48, c_1626])).
% 6.55/2.23  tff(c_1645, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1402, c_1644])).
% 6.55/2.23  tff(c_1593, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_1317])).
% 6.55/2.23  tff(c_1595, plain, (~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1593])).
% 6.55/2.23  tff(c_1647, plain, (~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_1595])).
% 6.55/2.23  tff(c_1910, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1895, c_1647])).
% 6.55/2.23  tff(c_1940, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_76, c_74, c_98, c_96, c_64, c_99, c_100, c_1910])).
% 6.55/2.23  tff(c_1942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_78, c_1940])).
% 6.55/2.23  tff(c_1944, plain, (m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_1593])).
% 6.55/2.23  tff(c_22, plain, (![F_27, A_22, B_23, D_25, C_24]: (r1_funct_2(A_22, B_23, C_24, D_25, F_27, F_27) | ~m1_subset_1(F_27, k1_zfmisc_1(k2_zfmisc_1(C_24, D_25))) | ~v1_funct_2(F_27, C_24, D_25) | ~m1_subset_1(F_27, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(F_27, A_22, B_23) | ~v1_funct_1(F_27) | v1_xboole_0(D_25) | v1_xboole_0(B_23))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.23  tff(c_1946, plain, (![A_22, B_23]: (r1_funct_2(A_22, B_23, u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), A_22, B_23) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_23))), inference(resolution, [status(thm)], [c_1944, c_22])).
% 6.55/2.23  tff(c_1966, plain, (![A_22, B_23]: (r1_funct_2(A_22, B_23, u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), A_22, B_23) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_23))), inference(demodulation, [status(thm), theory('equality')], [c_1594, c_1946])).
% 6.55/2.23  tff(c_1967, plain, (![A_22, B_23]: (r1_funct_2(A_22, B_23, u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), A_22, B_23) | v1_xboole_0(B_23))), inference(negUnitSimplification, [status(thm)], [c_1402, c_1966])).
% 6.55/2.23  tff(c_1989, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1967])).
% 6.55/2.23  tff(c_2033, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2030, c_1989])).
% 6.55/2.23  tff(c_2306, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_2303, c_2033])).
% 6.55/2.23  tff(c_2309, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_98, c_96, c_2306])).
% 6.55/2.23  tff(c_2311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2309])).
% 6.55/2.23  tff(c_2313, plain, (v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1967])).
% 6.55/2.23  tff(c_1943, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_1593])).
% 6.55/2.23  tff(c_2319, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2313, c_1943])).
% 6.55/2.23  tff(c_2371, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2370, c_2319])).
% 6.55/2.23  tff(c_1196, plain, (![A_439, B_440, C_441, D_442]: (k2_partfun1(A_439, B_440, C_441, D_442)=k7_relat_1(C_441, D_442) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(A_439, B_440))) | ~v1_funct_1(C_441))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.55/2.23  tff(c_1198, plain, (![D_442]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_442)=k7_relat_1('#skF_5', D_442) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_100, c_1196])).
% 6.55/2.23  tff(c_1205, plain, (![D_442]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_442)=k7_relat_1('#skF_5', D_442))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1198])).
% 6.55/2.23  tff(c_2511, plain, (![A_655, B_656, C_657, D_658]: (k2_partfun1(u1_struct_0(A_655), u1_struct_0(B_656), C_657, u1_struct_0(D_658))=k2_tmap_1(A_655, B_656, C_657, D_658) | ~m1_pre_topc(D_658, A_655) | ~m1_subset_1(C_657, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_655), u1_struct_0(B_656)))) | ~v1_funct_2(C_657, u1_struct_0(A_655), u1_struct_0(B_656)) | ~v1_funct_1(C_657) | ~l1_pre_topc(B_656) | ~v2_pre_topc(B_656) | v2_struct_0(B_656) | ~l1_pre_topc(A_655) | ~v2_pre_topc(A_655) | v2_struct_0(A_655))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.55/2.23  tff(c_2515, plain, (![D_658]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_658))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_658) | ~m1_pre_topc(D_658, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_100, c_2511])).
% 6.55/2.23  tff(c_2521, plain, (![D_658]: (k7_relat_1('#skF_5', u1_struct_0(D_658))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_658) | ~m1_pre_topc(D_658, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_76, c_74, c_64, c_99, c_1205, c_2515])).
% 6.55/2.23  tff(c_2528, plain, (![D_660]: (k7_relat_1('#skF_5', u1_struct_0(D_660))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_660) | ~m1_pre_topc(D_660, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_78, c_2521])).
% 6.55/2.23  tff(c_2534, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2528, c_167])).
% 6.55/2.23  tff(c_2543, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_2534])).
% 6.55/2.23  tff(c_2691, plain, (![D_687, E_688, C_685, B_689, F_686, A_684]: (r2_funct_2(u1_struct_0(D_687), u1_struct_0(B_689), k3_tmap_1(A_684, B_689, C_685, D_687, F_686), k2_tmap_1(A_684, B_689, E_688, D_687)) | ~m1_pre_topc(D_687, C_685) | ~r2_funct_2(u1_struct_0(C_685), u1_struct_0(B_689), F_686, k2_tmap_1(A_684, B_689, E_688, C_685)) | ~m1_subset_1(F_686, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_685), u1_struct_0(B_689)))) | ~v1_funct_2(F_686, u1_struct_0(C_685), u1_struct_0(B_689)) | ~v1_funct_1(F_686) | ~m1_subset_1(E_688, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_684), u1_struct_0(B_689)))) | ~v1_funct_2(E_688, u1_struct_0(A_684), u1_struct_0(B_689)) | ~v1_funct_1(E_688) | ~m1_pre_topc(D_687, A_684) | v2_struct_0(D_687) | ~m1_pre_topc(C_685, A_684) | v2_struct_0(C_685) | ~l1_pre_topc(B_689) | ~v2_pre_topc(B_689) | v2_struct_0(B_689) | ~l1_pre_topc(A_684) | ~v2_pre_topc(A_684) | v2_struct_0(A_684))), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.55/2.23  tff(c_2693, plain, (![D_687, F_686]: (r2_funct_2(u1_struct_0(D_687), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', D_687, F_686), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_687)) | ~m1_pre_topc(D_687, '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), F_686, '#skF_5') | ~m1_subset_1(F_686, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_686, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_686) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_687, '#skF_4') | v2_struct_0(D_687) | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2543, c_2691])).
% 6.55/2.23  tff(c_2695, plain, (![D_687, F_686]: (r2_funct_2(u1_struct_0(D_687), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', D_687, F_686), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_687)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), F_686, '#skF_5') | ~m1_subset_1(F_686, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_686, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_686) | ~m1_pre_topc(D_687, '#skF_4') | v2_struct_0(D_687) | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95, c_76, c_74, c_98, c_64, c_99, c_100, c_2693])).
% 6.55/2.23  tff(c_2783, plain, (![D_712, F_713]: (r2_funct_2(u1_struct_0(D_712), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', D_712, F_713), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_712)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), F_713, '#skF_5') | ~m1_subset_1(F_713, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_713, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_713) | ~m1_pre_topc(D_712, '#skF_4') | v2_struct_0(D_712))), inference(negUnitSimplification, [status(thm)], [c_68, c_78, c_2695])).
% 6.55/2.23  tff(c_2793, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2371, c_2783])).
% 6.55/2.23  tff(c_2803, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_99, c_100, c_1250, c_2793])).
% 6.55/2.23  tff(c_2804, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2803])).
% 6.55/2.23  tff(c_14, plain, (![D_16, C_15, A_13, B_14]: (D_16=C_15 | ~r2_funct_2(A_13, B_14, C_15, D_16) | ~m1_subset_1(D_16, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(D_16, A_13, B_14) | ~v1_funct_1(D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.55/2.23  tff(c_2808, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_2804, c_14])).
% 6.55/2.23  tff(c_2815, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2808])).
% 6.55/2.23  tff(c_2833, plain, (~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2815])).
% 6.55/2.23  tff(c_2836, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1336, c_2833])).
% 6.55/2.23  tff(c_2840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1283, c_2836])).
% 6.55/2.23  tff(c_2842, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_2815])).
% 6.55/2.23  tff(c_28, plain, (![A_43, B_44, C_45, D_46]: (m1_subset_1(k2_tmap_1(A_43, B_44, C_45, D_46), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_46), u1_struct_0(B_44)))) | ~l1_struct_0(D_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), u1_struct_0(B_44)))) | ~v1_funct_2(C_45, u1_struct_0(A_43), u1_struct_0(B_44)) | ~v1_funct_1(C_45) | ~l1_struct_0(B_44) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.55/2.23  tff(c_2841, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_2815])).
% 6.55/2.23  tff(c_2910, plain, (~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_2841])).
% 6.55/2.23  tff(c_2913, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_2910])).
% 6.55/2.23  tff(c_2917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1330, c_1293, c_64, c_99, c_100, c_1283, c_2913])).
% 6.55/2.23  tff(c_2919, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_2841])).
% 6.55/2.23  tff(c_38, plain, (![A_47, E_51, D_50, C_49, B_48]: (v1_funct_1(k3_tmap_1(A_47, B_48, C_49, D_50, E_51)) | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_49), u1_struct_0(B_48)))) | ~v1_funct_2(E_51, u1_struct_0(C_49), u1_struct_0(B_48)) | ~v1_funct_1(E_51) | ~m1_pre_topc(D_50, A_47) | ~m1_pre_topc(C_49, A_47) | ~l1_pre_topc(B_48) | ~v2_pre_topc(B_48) | v2_struct_0(B_48) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.55/2.23  tff(c_2937, plain, (![A_47, D_50]: (v1_funct_1(k3_tmap_1(A_47, '#skF_2', '#skF_3', D_50, k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc(D_50, A_47) | ~m1_pre_topc('#skF_3', A_47) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_2919, c_38])).
% 6.55/2.23  tff(c_2990, plain, (![A_47, D_50]: (v1_funct_1(k3_tmap_1(A_47, '#skF_2', '#skF_3', D_50, k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_50, A_47) | ~m1_pre_topc('#skF_3', A_47) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_2842, c_2937])).
% 6.55/2.23  tff(c_2991, plain, (![A_47, D_50]: (v1_funct_1(k3_tmap_1(A_47, '#skF_2', '#skF_3', D_50, k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_50, A_47) | ~m1_pre_topc('#skF_3', A_47) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(negUnitSimplification, [status(thm)], [c_78, c_2990])).
% 6.55/2.23  tff(c_3051, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2991])).
% 6.55/2.23  tff(c_3054, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1349, c_3051])).
% 6.55/2.23  tff(c_3058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1283, c_3054])).
% 6.55/2.23  tff(c_3060, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2991])).
% 6.55/2.23  tff(c_2918, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_2841])).
% 6.55/2.23  tff(c_3068, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3060, c_2918])).
% 6.55/2.23  tff(c_1174, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_101])).
% 6.55/2.23  tff(c_3078, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3068, c_1174])).
% 6.55/2.23  tff(c_3089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1256, c_3078])).
% 6.55/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.55/2.23  
% 6.55/2.23  Inference rules
% 6.55/2.23  ----------------------
% 6.55/2.23  #Ref     : 0
% 6.55/2.23  #Sup     : 551
% 6.55/2.23  #Fact    : 0
% 6.55/2.23  #Define  : 0
% 6.55/2.23  #Split   : 26
% 6.55/2.23  #Chain   : 0
% 6.55/2.23  #Close   : 0
% 6.55/2.23  
% 6.55/2.23  Ordering : KBO
% 6.55/2.23  
% 6.55/2.23  Simplification rules
% 6.55/2.23  ----------------------
% 6.55/2.23  #Subsume      : 48
% 6.55/2.23  #Demod        : 1290
% 6.55/2.23  #Tautology    : 263
% 6.55/2.23  #SimpNegUnit  : 112
% 6.55/2.23  #BackRed      : 108
% 6.55/2.23  
% 6.55/2.23  #Partial instantiations: 0
% 6.55/2.23  #Strategies tried      : 1
% 6.55/2.23  
% 6.55/2.23  Timing (in seconds)
% 6.55/2.23  ----------------------
% 6.55/2.23  Preprocessing        : 0.43
% 6.55/2.23  Parsing              : 0.23
% 6.55/2.23  CNF conversion       : 0.05
% 6.55/2.23  Main loop            : 0.97
% 6.55/2.23  Inferencing          : 0.34
% 6.55/2.23  Reduction            : 0.35
% 6.55/2.23  Demodulation         : 0.27
% 6.55/2.23  BG Simplification    : 0.04
% 6.55/2.23  Subsumption          : 0.17
% 6.55/2.23  Abstraction          : 0.04
% 6.55/2.23  MUC search           : 0.00
% 6.55/2.23  Cooper               : 0.00
% 6.55/2.23  Total                : 1.49
% 6.55/2.23  Index Insertion      : 0.00
% 6.55/2.23  Index Deletion       : 0.00
% 6.55/2.23  Index Matching       : 0.00
% 6.55/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
