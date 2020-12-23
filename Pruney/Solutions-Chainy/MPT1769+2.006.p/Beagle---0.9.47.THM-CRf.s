%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:18 EST 2020

% Result     : Theorem 5.71s
% Output     : CNFRefutation 6.26s
% Verified   : 
% Statistics : Number of formulae       :  270 (4478 expanded)
%              Number of leaves         :   46 (1683 expanded)
%              Depth                    :   23
%              Number of atoms          :  854 (41250 expanded)
%              Number of equality atoms :   52 (2369 expanded)
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

tff(f_291,negated_conjecture,(
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

tff(f_68,axiom,(
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

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_154,axiom,(
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

tff(f_184,axiom,(
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

tff(f_109,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_136,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

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
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_58,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_242,plain,(
    ! [A_237,B_238,D_239] :
      ( r2_funct_2(A_237,B_238,D_239,D_239)
      | ~ m1_subset_1(D_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ v1_funct_2(D_239,A_237,B_238)
      | ~ v1_funct_1(D_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_248,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_242])).

tff(c_257,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_248])).

tff(c_48,plain,(
    '#skF_1' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_82,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_97,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_82])).

tff(c_72,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_98,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_72])).

tff(c_112,plain,(
    ! [B_216,A_217] :
      ( l1_pre_topc(B_216)
      | ~ m1_pre_topc(B_216,A_217)
      | ~ l1_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_115,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_112])).

tff(c_121,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_115])).

tff(c_18,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_54,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_52,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_1151,plain,(
    ! [A_393,B_394,C_395,D_396] :
      ( v1_funct_1(k2_tmap_1(A_393,B_394,C_395,D_396))
      | ~ l1_struct_0(D_396)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_393),u1_struct_0(B_394))))
      | ~ v1_funct_2(C_395,u1_struct_0(A_393),u1_struct_0(B_394))
      | ~ v1_funct_1(C_395)
      | ~ l1_struct_0(B_394)
      | ~ l1_struct_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1153,plain,(
    ! [D_396] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_396))
      | ~ l1_struct_0(D_396)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_1151])).

tff(c_1160,plain,(
    ! [D_396] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_396))
      | ~ l1_struct_0(D_396)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1153])).

tff(c_1167,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1160])).

tff(c_1171,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_1167])).

tff(c_1175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_1171])).

tff(c_1176,plain,(
    ! [D_396] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_396))
      | ~ l1_struct_0(D_396) ) ),
    inference(splitRight,[status(thm)],[c_1160])).

tff(c_1178,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1176])).

tff(c_1181,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_1178])).

tff(c_1185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1181])).

tff(c_1187,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1176])).

tff(c_1157,plain,(
    ! [D_396] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_396))
      | ~ l1_struct_0(D_396)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_1151])).

tff(c_1166,plain,(
    ! [D_396] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_396))
      | ~ l1_struct_0(D_396)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1157])).

tff(c_1214,plain,(
    ! [D_396] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_396))
      | ~ l1_struct_0(D_396)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_1166])).

tff(c_1215,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1214])).

tff(c_1218,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1215])).

tff(c_1222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_1218])).

tff(c_1224,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1214])).

tff(c_1177,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1160])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_101,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_64])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_102,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_1229,plain,(
    ! [A_404,B_405,C_406,D_407] :
      ( v1_funct_2(k2_tmap_1(A_404,B_405,C_406,D_407),u1_struct_0(D_407),u1_struct_0(B_405))
      | ~ l1_struct_0(D_407)
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_404),u1_struct_0(B_405))))
      | ~ v1_funct_2(C_406,u1_struct_0(A_404),u1_struct_0(B_405))
      | ~ v1_funct_1(C_406)
      | ~ l1_struct_0(B_405)
      | ~ l1_struct_0(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1233,plain,(
    ! [D_407] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_407),u1_struct_0(D_407),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_407)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_102,c_1229])).

tff(c_1241,plain,(
    ! [D_407] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_407),u1_struct_0(D_407),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_1187,c_66,c_101,c_1233])).

tff(c_30,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( m1_subset_1(k2_tmap_1(A_45,B_46,C_47,D_48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_48),u1_struct_0(B_46))))
      | ~ l1_struct_0(D_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_45),u1_struct_0(B_46))))
      | ~ v1_funct_2(C_47,u1_struct_0(A_45),u1_struct_0(B_46))
      | ~ v1_funct_1(C_47)
      | ~ l1_struct_0(B_46)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1155,plain,(
    ! [D_396] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_396))
      | ~ l1_struct_0(D_396)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_102,c_1151])).

tff(c_1163,plain,(
    ! [D_396] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_396))
      | ~ l1_struct_0(D_396)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_101,c_1155])).

tff(c_1226,plain,(
    ! [D_396] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_396))
      | ~ l1_struct_0(D_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_1187,c_1163])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_84,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_96,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_84])).

tff(c_68,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_100,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_68])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_78,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_1820,plain,(
    ! [D_497,C_493,E_494,A_496,B_495] :
      ( v1_funct_2(k3_tmap_1(A_496,B_495,C_493,D_497,E_494),u1_struct_0(D_497),u1_struct_0(B_495))
      | ~ m1_subset_1(E_494,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_493),u1_struct_0(B_495))))
      | ~ v1_funct_2(E_494,u1_struct_0(C_493),u1_struct_0(B_495))
      | ~ v1_funct_1(E_494)
      | ~ m1_pre_topc(D_497,A_496)
      | ~ m1_pre_topc(C_493,A_496)
      | ~ l1_pre_topc(B_495)
      | ~ v2_pre_topc(B_495)
      | v2_struct_0(B_495)
      | ~ l1_pre_topc(A_496)
      | ~ v2_pre_topc(A_496)
      | v2_struct_0(A_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1826,plain,(
    ! [A_496,D_497] :
      ( v1_funct_2(k3_tmap_1(A_496,'#skF_2','#skF_4',D_497,'#skF_5'),u1_struct_0(D_497),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_497,A_496)
      | ~ m1_pre_topc('#skF_4',A_496)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_496)
      | ~ v2_pre_topc(A_496)
      | v2_struct_0(A_496) ) ),
    inference(resolution,[status(thm)],[c_102,c_1820])).

tff(c_1836,plain,(
    ! [A_496,D_497] :
      ( v1_funct_2(k3_tmap_1(A_496,'#skF_2','#skF_4',D_497,'#skF_5'),u1_struct_0(D_497),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_497,A_496)
      | ~ m1_pre_topc('#skF_4',A_496)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_496)
      | ~ v2_pre_topc(A_496)
      | v2_struct_0(A_496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_101,c_1826])).

tff(c_1842,plain,(
    ! [A_498,D_499] :
      ( v1_funct_2(k3_tmap_1(A_498,'#skF_2','#skF_4',D_499,'#skF_5'),u1_struct_0(D_499),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_499,A_498)
      | ~ m1_pre_topc('#skF_4',A_498)
      | ~ l1_pre_topc(A_498)
      | ~ v2_pre_topc(A_498)
      | v2_struct_0(A_498) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1836])).

tff(c_1468,plain,(
    ! [C_454,D_458,B_456,E_455,A_457] :
      ( v1_funct_1(k3_tmap_1(A_457,B_456,C_454,D_458,E_455))
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_454),u1_struct_0(B_456))))
      | ~ v1_funct_2(E_455,u1_struct_0(C_454),u1_struct_0(B_456))
      | ~ v1_funct_1(E_455)
      | ~ m1_pre_topc(D_458,A_457)
      | ~ m1_pre_topc(C_454,A_457)
      | ~ l1_pre_topc(B_456)
      | ~ v2_pre_topc(B_456)
      | v2_struct_0(B_456)
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1472,plain,(
    ! [A_457,D_458] :
      ( v1_funct_1(k3_tmap_1(A_457,'#skF_2','#skF_4',D_458,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_458,A_457)
      | ~ m1_pre_topc('#skF_4',A_457)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(resolution,[status(thm)],[c_102,c_1468])).

tff(c_1478,plain,(
    ! [A_457,D_458] :
      ( v1_funct_1(k3_tmap_1(A_457,'#skF_2','#skF_4',D_458,'#skF_5'))
      | ~ m1_pre_topc(D_458,A_457)
      | ~ m1_pre_topc('#skF_4',A_457)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_101,c_1472])).

tff(c_1479,plain,(
    ! [A_457,D_458] :
      ( v1_funct_1(k3_tmap_1(A_457,'#skF_2','#skF_4',D_458,'#skF_5'))
      | ~ m1_pre_topc(D_458,A_457)
      | ~ m1_pre_topc('#skF_4',A_457)
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1478])).

tff(c_1247,plain,(
    ! [F_412,C_410,B_411,D_414,A_413] :
      ( r1_funct_2(A_413,B_411,C_410,D_414,F_412,F_412)
      | ~ m1_subset_1(F_412,k1_zfmisc_1(k2_zfmisc_1(C_410,D_414)))
      | ~ v1_funct_2(F_412,C_410,D_414)
      | ~ m1_subset_1(F_412,k1_zfmisc_1(k2_zfmisc_1(A_413,B_411)))
      | ~ v1_funct_2(F_412,A_413,B_411)
      | ~ v1_funct_1(F_412)
      | v1_xboole_0(D_414)
      | v1_xboole_0(B_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1249,plain,(
    ! [A_413,B_411] :
      ( r1_funct_2(A_413,B_411,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_7','#skF_7')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_413,B_411)))
      | ~ v1_funct_2('#skF_7',A_413,B_411)
      | ~ v1_funct_1('#skF_7')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_411) ) ),
    inference(resolution,[status(thm)],[c_50,c_1247])).

tff(c_1256,plain,(
    ! [A_413,B_411] :
      ( r1_funct_2(A_413,B_411,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_7','#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_413,B_411)))
      | ~ v1_funct_2('#skF_7',A_413,B_411)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1249])).

tff(c_1264,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1256])).

tff(c_22,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(u1_struct_0(A_23))
      | ~ l1_struct_0(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1267,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1264,c_22])).

tff(c_1270,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_1267])).

tff(c_1272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1270])).

tff(c_1274,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1256])).

tff(c_46,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_104,plain,(
    r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_1356,plain,(
    ! [F_442,C_439,B_440,D_444,A_443,E_441] :
      ( F_442 = E_441
      | ~ r1_funct_2(A_443,B_440,C_439,D_444,E_441,F_442)
      | ~ m1_subset_1(F_442,k1_zfmisc_1(k2_zfmisc_1(C_439,D_444)))
      | ~ v1_funct_2(F_442,C_439,D_444)
      | ~ v1_funct_1(F_442)
      | ~ m1_subset_1(E_441,k1_zfmisc_1(k2_zfmisc_1(A_443,B_440)))
      | ~ v1_funct_2(E_441,A_443,B_440)
      | ~ v1_funct_1(E_441)
      | v1_xboole_0(D_444)
      | v1_xboole_0(B_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1364,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_104,c_1356])).

tff(c_1382,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_101,c_102,c_54,c_52,c_50,c_1364])).

tff(c_1383,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1274,c_1382])).

tff(c_294,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( v1_funct_1(k2_tmap_1(A_244,B_245,C_246,D_247))
      | ~ l1_struct_0(D_247)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_244),u1_struct_0(B_245))))
      | ~ v1_funct_2(C_246,u1_struct_0(A_244),u1_struct_0(B_245))
      | ~ v1_funct_1(C_246)
      | ~ l1_struct_0(B_245)
      | ~ l1_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_296,plain,(
    ! [D_247] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_247))
      | ~ l1_struct_0(D_247)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_294])).

tff(c_303,plain,(
    ! [D_247] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_247))
      | ~ l1_struct_0(D_247)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_296])).

tff(c_310,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_313,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_310])).

tff(c_317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_313])).

tff(c_318,plain,(
    ! [D_247] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_247))
      | ~ l1_struct_0(D_247) ) ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_330,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_333,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_330])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_333])).

tff(c_339,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_587,plain,(
    ! [F_290,B_289,C_288,A_291,D_292] :
      ( r1_funct_2(A_291,B_289,C_288,D_292,F_290,F_290)
      | ~ m1_subset_1(F_290,k1_zfmisc_1(k2_zfmisc_1(C_288,D_292)))
      | ~ v1_funct_2(F_290,C_288,D_292)
      | ~ m1_subset_1(F_290,k1_zfmisc_1(k2_zfmisc_1(A_291,B_289)))
      | ~ v1_funct_2(F_290,A_291,B_289)
      | ~ v1_funct_1(F_290)
      | v1_xboole_0(D_292)
      | v1_xboole_0(B_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_589,plain,(
    ! [A_291,B_289] :
      ( r1_funct_2(A_291,B_289,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_7','#skF_7')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_291,B_289)))
      | ~ v1_funct_2('#skF_7',A_291,B_289)
      | ~ v1_funct_1('#skF_7')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_289) ) ),
    inference(resolution,[status(thm)],[c_50,c_587])).

tff(c_596,plain,(
    ! [A_291,B_289] :
      ( r1_funct_2(A_291,B_289,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_7','#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_291,B_289)))
      | ~ v1_funct_2('#skF_7',A_291,B_289)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_589])).

tff(c_611,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_596])).

tff(c_614,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_611,c_22])).

tff(c_617,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_614])).

tff(c_619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_617])).

tff(c_621,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_596])).

tff(c_737,plain,(
    ! [E_323,A_325,B_322,D_326,C_321,F_324] :
      ( F_324 = E_323
      | ~ r1_funct_2(A_325,B_322,C_321,D_326,E_323,F_324)
      | ~ m1_subset_1(F_324,k1_zfmisc_1(k2_zfmisc_1(C_321,D_326)))
      | ~ v1_funct_2(F_324,C_321,D_326)
      | ~ v1_funct_1(F_324)
      | ~ m1_subset_1(E_323,k1_zfmisc_1(k2_zfmisc_1(A_325,B_322)))
      | ~ v1_funct_2(E_323,A_325,B_322)
      | ~ v1_funct_1(E_323)
      | v1_xboole_0(D_326)
      | v1_xboole_0(B_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_745,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_104,c_737])).

tff(c_763,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_101,c_102,c_54,c_52,c_50,c_745])).

tff(c_764,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_621,c_763])).

tff(c_88,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_103,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_88])).

tff(c_258,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_771,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_258])).

tff(c_300,plain,(
    ! [D_247] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_247))
      | ~ l1_struct_0(D_247)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_294])).

tff(c_309,plain,(
    ! [D_247] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_247))
      | ~ l1_struct_0(D_247)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_300])).

tff(c_320,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_323,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_320])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_323])).

tff(c_329,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_319,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_513,plain,(
    ! [A_278,B_279,C_280,D_281] :
      ( v1_funct_2(k2_tmap_1(A_278,B_279,C_280,D_281),u1_struct_0(D_281),u1_struct_0(B_279))
      | ~ l1_struct_0(D_281)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_278),u1_struct_0(B_279))))
      | ~ v1_funct_2(C_280,u1_struct_0(A_278),u1_struct_0(B_279))
      | ~ v1_funct_1(C_280)
      | ~ l1_struct_0(B_279)
      | ~ l1_struct_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_519,plain,(
    ! [D_281] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_281),u1_struct_0(D_281),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_281)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_102,c_513])).

tff(c_535,plain,(
    ! [D_283] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_283),u1_struct_0(D_283),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_339,c_66,c_101,c_519])).

tff(c_433,plain,(
    ! [A_273,B_274,C_275,D_276] :
      ( m1_subset_1(k2_tmap_1(A_273,B_274,C_275,D_276),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_276),u1_struct_0(B_274))))
      | ~ l1_struct_0(D_276)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_273),u1_struct_0(B_274))))
      | ~ v1_funct_2(C_275,u1_struct_0(A_273),u1_struct_0(B_274))
      | ~ v1_funct_1(C_275)
      | ~ l1_struct_0(B_274)
      | ~ l1_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_298,plain,(
    ! [D_247] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_247))
      | ~ l1_struct_0(D_247)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_102,c_294])).

tff(c_306,plain,(
    ! [D_247] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_247))
      | ~ l1_struct_0(D_247)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_101,c_298])).

tff(c_369,plain,(
    ! [D_247] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_247))
      | ~ l1_struct_0(D_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_339,c_306])).

tff(c_94,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_291])).

tff(c_99,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_94])).

tff(c_293,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_99])).

tff(c_340,plain,(
    ! [D_248,C_249,A_250,B_251] :
      ( D_248 = C_249
      | ~ r2_funct_2(A_250,B_251,C_249,D_248)
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251)))
      | ~ v1_funct_2(D_248,A_250,B_251)
      | ~ v1_funct_1(D_248)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251)))
      | ~ v1_funct_2(C_249,A_250,B_251)
      | ~ v1_funct_1(C_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_342,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_293,c_340])).

tff(c_351,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_342])).

tff(c_371,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_374,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_369,c_371])).

tff(c_378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_374])).

tff(c_379,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_381,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_440,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_433,c_381])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_339,c_66,c_101,c_102,c_329,c_440])).

tff(c_462,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_493,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_462])).

tff(c_538,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_535,c_493])).

tff(c_542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_538])).

tff(c_543,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_462])).

tff(c_217,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( k2_partfun1(A_232,B_233,C_234,D_235) = k7_relat_1(C_234,D_235)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ v1_funct_1(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_221,plain,(
    ! [D_235] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_235) = k7_relat_1('#skF_5',D_235)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_102,c_217])).

tff(c_229,plain,(
    ! [D_235] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_235) = k7_relat_1('#skF_5',D_235) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_221])).

tff(c_864,plain,(
    ! [A_344,B_345,C_346,D_347] :
      ( k2_partfun1(u1_struct_0(A_344),u1_struct_0(B_345),C_346,u1_struct_0(D_347)) = k2_tmap_1(A_344,B_345,C_346,D_347)
      | ~ m1_pre_topc(D_347,A_344)
      | ~ m1_subset_1(C_346,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_344),u1_struct_0(B_345))))
      | ~ v1_funct_2(C_346,u1_struct_0(A_344),u1_struct_0(B_345))
      | ~ v1_funct_1(C_346)
      | ~ l1_pre_topc(B_345)
      | ~ v2_pre_topc(B_345)
      | v2_struct_0(B_345)
      | ~ l1_pre_topc(A_344)
      | ~ v2_pre_topc(A_344)
      | v2_struct_0(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_868,plain,(
    ! [D_347] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_347)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_347)
      | ~ m1_pre_topc(D_347,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_102,c_864])).

tff(c_874,plain,(
    ! [D_347] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_347)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_347)
      | ~ m1_pre_topc(D_347,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_97,c_78,c_76,c_66,c_101,c_229,c_868])).

tff(c_880,plain,(
    ! [D_348] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_348)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_348)
      | ~ m1_pre_topc(D_348,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_80,c_874])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_125,plain,(
    ! [B_218,A_219] :
      ( v1_relat_1(B_218)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(A_219))
      | ~ v1_relat_1(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_102,c_125])).

tff(c_134,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_128])).

tff(c_144,plain,(
    ! [C_220,A_221,B_222] :
      ( v4_relat_1(C_220,A_221)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_155,plain,(
    v4_relat_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_102,c_144])).

tff(c_170,plain,(
    ! [B_226,A_227] :
      ( k7_relat_1(B_226,A_227) = B_226
      | ~ v4_relat_1(B_226,A_227)
      | ~ v1_relat_1(B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_173,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_155,c_170])).

tff(c_182,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_173])).

tff(c_886,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_182])).

tff(c_895,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_886])).

tff(c_1065,plain,(
    ! [C_386,D_383,A_385,E_387,B_384] :
      ( r2_funct_2(u1_struct_0(C_386),u1_struct_0(B_384),k3_tmap_1(A_385,B_384,D_383,C_386,k2_tmap_1(A_385,B_384,E_387,D_383)),k2_tmap_1(A_385,B_384,E_387,C_386))
      | ~ m1_pre_topc(C_386,D_383)
      | ~ m1_subset_1(E_387,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385),u1_struct_0(B_384))))
      | ~ v1_funct_2(E_387,u1_struct_0(A_385),u1_struct_0(B_384))
      | ~ v1_funct_1(E_387)
      | ~ m1_pre_topc(D_383,A_385)
      | v2_struct_0(D_383)
      | ~ m1_pre_topc(C_386,A_385)
      | v2_struct_0(C_386)
      | ~ l1_pre_topc(B_384)
      | ~ v2_pre_topc(B_384)
      | v2_struct_0(B_384)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_1070,plain,(
    ! [C_386] :
      ( r2_funct_2(u1_struct_0(C_386),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_386,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_386))
      | ~ m1_pre_topc(C_386,'#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_386,'#skF_4')
      | v2_struct_0(C_386)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_1065])).

tff(c_1082,plain,(
    ! [C_386] :
      ( r2_funct_2(u1_struct_0(C_386),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_386,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_386))
      | ~ m1_pre_topc(C_386,'#skF_4')
      | v2_struct_0(C_386)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_97,c_78,c_76,c_100,c_66,c_101,c_102,c_1070])).

tff(c_1093,plain,(
    ! [C_388] :
      ( r2_funct_2(u1_struct_0(C_388),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_388,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_388))
      | ~ m1_pre_topc(C_388,'#skF_4')
      | v2_struct_0(C_388) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_80,c_1082])).

tff(c_1101,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_1093])).

tff(c_1107,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1101])).

tff(c_1109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_771,c_1107])).

tff(c_1111,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_1188,plain,(
    ! [D_397,C_398,A_399,B_400] :
      ( D_397 = C_398
      | ~ r2_funct_2(A_399,B_400,C_398,D_397)
      | ~ m1_subset_1(D_397,k1_zfmisc_1(k2_zfmisc_1(A_399,B_400)))
      | ~ v1_funct_2(D_397,A_399,B_400)
      | ~ v1_funct_1(D_397)
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1(A_399,B_400)))
      | ~ v1_funct_2(C_398,A_399,B_400)
      | ~ v1_funct_1(C_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1190,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1111,c_1188])).

tff(c_1199,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7') = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1190])).

tff(c_1486,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_1383,c_1383,c_1383,c_1199])).

tff(c_1487,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1486])).

tff(c_1491,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1479,c_1487])).

tff(c_1494,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_97,c_100,c_98,c_1491])).

tff(c_1496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1494])).

tff(c_1498,plain,(
    v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1486])).

tff(c_1610,plain,(
    ! [B_484,C_482,D_486,E_483,A_485] :
      ( m1_subset_1(k3_tmap_1(A_485,B_484,C_482,D_486,E_483),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_486),u1_struct_0(B_484))))
      | ~ m1_subset_1(E_483,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_482),u1_struct_0(B_484))))
      | ~ v1_funct_2(E_483,u1_struct_0(C_482),u1_struct_0(B_484))
      | ~ v1_funct_1(E_483)
      | ~ m1_pre_topc(D_486,A_485)
      | ~ m1_pre_topc(C_482,A_485)
      | ~ l1_pre_topc(B_484)
      | ~ v2_pre_topc(B_484)
      | v2_struct_0(B_484)
      | ~ l1_pre_topc(A_485)
      | ~ v2_pre_topc(A_485)
      | v2_struct_0(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1497,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1486])).

tff(c_1499,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1497])).

tff(c_1619,plain,
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
    inference(resolution,[status(thm)],[c_1610,c_1499])).

tff(c_1652,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_97,c_78,c_76,c_100,c_98,c_66,c_101,c_102,c_1619])).

tff(c_1654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_80,c_1652])).

tff(c_1656,plain,(
    m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1497])).

tff(c_40,plain,(
    ! [D_52,C_51,B_50,A_49,E_53] :
      ( v1_funct_1(k3_tmap_1(A_49,B_50,C_51,D_52,E_53))
      | ~ m1_subset_1(E_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_51),u1_struct_0(B_50))))
      | ~ v1_funct_2(E_53,u1_struct_0(C_51),u1_struct_0(B_50))
      | ~ v1_funct_1(E_53)
      | ~ m1_pre_topc(D_52,A_49)
      | ~ m1_pre_topc(C_51,A_49)
      | ~ l1_pre_topc(B_50)
      | ~ v2_pre_topc(B_50)
      | v2_struct_0(B_50)
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1658,plain,(
    ! [A_49,D_52] :
      ( v1_funct_1(k3_tmap_1(A_49,'#skF_2','#skF_3',D_52,k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')))
      | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'))
      | ~ m1_pre_topc(D_52,A_49)
      | ~ m1_pre_topc('#skF_3',A_49)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_1656,c_40])).

tff(c_1686,plain,(
    ! [A_49,D_52] :
      ( v1_funct_1(k3_tmap_1(A_49,'#skF_2','#skF_3',D_52,k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')))
      | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_52,A_49)
      | ~ m1_pre_topc('#skF_3',A_49)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1498,c_1658])).

tff(c_1687,plain,(
    ! [A_49,D_52] :
      ( v1_funct_1(k3_tmap_1(A_49,'#skF_2','#skF_3',D_52,k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')))
      | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_52,A_49)
      | ~ m1_pre_topc('#skF_3',A_49)
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1686])).

tff(c_1718,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1687])).

tff(c_1845,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1842,c_1718])).

tff(c_1848,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_97,c_100,c_98,c_1845])).

tff(c_1850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1848])).

tff(c_1852,plain,(
    v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1687])).

tff(c_1655,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1497])).

tff(c_1865,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1852,c_1655])).

tff(c_1898,plain,(
    ! [A_502,B_503,C_504,D_505] :
      ( k2_partfun1(u1_struct_0(A_502),u1_struct_0(B_503),C_504,u1_struct_0(D_505)) = k2_tmap_1(A_502,B_503,C_504,D_505)
      | ~ m1_pre_topc(D_505,A_502)
      | ~ m1_subset_1(C_504,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_502),u1_struct_0(B_503))))
      | ~ v1_funct_2(C_504,u1_struct_0(A_502),u1_struct_0(B_503))
      | ~ v1_funct_1(C_504)
      | ~ l1_pre_topc(B_503)
      | ~ v2_pre_topc(B_503)
      | v2_struct_0(B_503)
      | ~ l1_pre_topc(A_502)
      | ~ v2_pre_topc(A_502)
      | v2_struct_0(A_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1902,plain,(
    ! [D_505] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_505)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_505)
      | ~ m1_pre_topc(D_505,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_102,c_1898])).

tff(c_1908,plain,(
    ! [D_505] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_505)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_505)
      | ~ m1_pre_topc(D_505,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_97,c_78,c_76,c_66,c_101,c_229,c_1902])).

tff(c_1914,plain,(
    ! [D_506] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_506)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_506)
      | ~ m1_pre_topc(D_506,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_80,c_1908])).

tff(c_1920,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1914,c_182])).

tff(c_1929,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1920])).

tff(c_2123,plain,(
    ! [E_539,B_536,D_535,A_537,C_538] :
      ( r2_funct_2(u1_struct_0(C_538),u1_struct_0(B_536),k3_tmap_1(A_537,B_536,D_535,C_538,k2_tmap_1(A_537,B_536,E_539,D_535)),k2_tmap_1(A_537,B_536,E_539,C_538))
      | ~ m1_pre_topc(C_538,D_535)
      | ~ m1_subset_1(E_539,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_537),u1_struct_0(B_536))))
      | ~ v1_funct_2(E_539,u1_struct_0(A_537),u1_struct_0(B_536))
      | ~ v1_funct_1(E_539)
      | ~ m1_pre_topc(D_535,A_537)
      | v2_struct_0(D_535)
      | ~ m1_pre_topc(C_538,A_537)
      | v2_struct_0(C_538)
      | ~ l1_pre_topc(B_536)
      | ~ v2_pre_topc(B_536)
      | v2_struct_0(B_536)
      | ~ l1_pre_topc(A_537)
      | ~ v2_pre_topc(A_537)
      | v2_struct_0(A_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_2128,plain,(
    ! [C_538] :
      ( r2_funct_2(u1_struct_0(C_538),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_538,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_538))
      | ~ m1_pre_topc(C_538,'#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_538,'#skF_4')
      | v2_struct_0(C_538)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1929,c_2123])).

tff(c_2134,plain,(
    ! [C_538] :
      ( r2_funct_2(u1_struct_0(C_538),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_538,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_538))
      | ~ m1_pre_topc(C_538,'#skF_4')
      | v2_struct_0(C_538)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_97,c_78,c_76,c_100,c_66,c_101,c_102,c_2128])).

tff(c_2147,plain,(
    ! [C_544] :
      ( r2_funct_2(u1_struct_0(C_544),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_544,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_544))
      | ~ m1_pre_topc(C_544,'#skF_4')
      | v2_struct_0(C_544) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_80,c_2134])).

tff(c_2155,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1865,c_2147])).

tff(c_2161,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_2155])).

tff(c_2162,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2161])).

tff(c_16,plain,(
    ! [D_18,C_17,A_15,B_16] :
      ( D_18 = C_17
      | ~ r2_funct_2(A_15,B_16,C_17,D_18)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_funct_2(D_18,A_15,B_16)
      | ~ v1_funct_1(D_18)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2164,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2162,c_16])).

tff(c_2167,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_2164])).

tff(c_2185,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2167])).

tff(c_2188,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1226,c_2185])).

tff(c_2192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_2188])).

tff(c_2193,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2167])).

tff(c_2222,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2193])).

tff(c_2240,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_2222])).

tff(c_2244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_1187,c_66,c_101,c_102,c_1224,c_2240])).

tff(c_2245,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2193])).

tff(c_2384,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2245])).

tff(c_2387,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1241,c_2384])).

tff(c_2391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_2387])).

tff(c_2392,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2245])).

tff(c_1110,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_2412,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_1110])).

tff(c_2422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_2412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:27:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.71/2.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.05  
% 5.71/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.71/2.06  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.71/2.06  
% 5.71/2.06  %Foreground sorts:
% 5.71/2.06  
% 5.71/2.06  
% 5.71/2.06  %Background operators:
% 5.71/2.06  
% 5.71/2.06  
% 5.71/2.06  %Foreground operators:
% 5.71/2.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.71/2.06  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.71/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.71/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.71/2.06  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.71/2.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.71/2.06  tff('#skF_7', type, '#skF_7': $i).
% 5.71/2.06  tff('#skF_5', type, '#skF_5': $i).
% 5.71/2.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.71/2.06  tff('#skF_6', type, '#skF_6': $i).
% 5.71/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.71/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.71/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.71/2.06  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.71/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.71/2.06  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.71/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.71/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.71/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.71/2.06  tff('#skF_4', type, '#skF_4': $i).
% 5.71/2.06  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 5.71/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.71/2.06  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.71/2.06  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.71/2.06  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.71/2.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.71/2.06  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.71/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.71/2.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.71/2.06  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.71/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.71/2.06  
% 6.26/2.12  tff(f_291, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 6.26/2.12  tff(f_68, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 6.26/2.12  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.26/2.12  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.26/2.12  tff(f_154, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 6.26/2.12  tff(f_184, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 6.26/2.12  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 6.26/2.12  tff(f_87, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.26/2.12  tff(f_52, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.26/2.12  tff(f_136, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.26/2.12  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.26/2.12  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.26/2.12  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.26/2.12  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 6.26/2.12  tff(f_222, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 6.26/2.12  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_58, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_242, plain, (![A_237, B_238, D_239]: (r2_funct_2(A_237, B_238, D_239, D_239) | ~m1_subset_1(D_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~v1_funct_2(D_239, A_237, B_238) | ~v1_funct_1(D_239))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.26/2.12  tff(c_248, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_242])).
% 6.26/2.12  tff(c_257, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_248])).
% 6.26/2.12  tff(c_48, plain, ('#skF_1'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_82, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_97, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_82])).
% 6.26/2.12  tff(c_72, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_98, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_72])).
% 6.26/2.12  tff(c_112, plain, (![B_216, A_217]: (l1_pre_topc(B_216) | ~m1_pre_topc(B_216, A_217) | ~l1_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.26/2.12  tff(c_115, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_98, c_112])).
% 6.26/2.12  tff(c_121, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_115])).
% 6.26/2.12  tff(c_18, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.26/2.12  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_54, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_52, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_1151, plain, (![A_393, B_394, C_395, D_396]: (v1_funct_1(k2_tmap_1(A_393, B_394, C_395, D_396)) | ~l1_struct_0(D_396) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_393), u1_struct_0(B_394)))) | ~v1_funct_2(C_395, u1_struct_0(A_393), u1_struct_0(B_394)) | ~v1_funct_1(C_395) | ~l1_struct_0(B_394) | ~l1_struct_0(A_393))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.26/2.12  tff(c_1153, plain, (![D_396]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_396)) | ~l1_struct_0(D_396) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_1151])).
% 6.26/2.12  tff(c_1160, plain, (![D_396]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_396)) | ~l1_struct_0(D_396) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1153])).
% 6.26/2.12  tff(c_1167, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1160])).
% 6.26/2.12  tff(c_1171, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_1167])).
% 6.26/2.12  tff(c_1175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_1171])).
% 6.26/2.12  tff(c_1176, plain, (![D_396]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_396)) | ~l1_struct_0(D_396))), inference(splitRight, [status(thm)], [c_1160])).
% 6.26/2.12  tff(c_1178, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1176])).
% 6.26/2.12  tff(c_1181, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_1178])).
% 6.26/2.12  tff(c_1185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_1181])).
% 6.26/2.12  tff(c_1187, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1176])).
% 6.26/2.12  tff(c_1157, plain, (![D_396]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_396)) | ~l1_struct_0(D_396) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_1151])).
% 6.26/2.12  tff(c_1166, plain, (![D_396]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_396)) | ~l1_struct_0(D_396) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1157])).
% 6.26/2.12  tff(c_1214, plain, (![D_396]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_396)) | ~l1_struct_0(D_396) | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_1166])).
% 6.26/2.12  tff(c_1215, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1214])).
% 6.26/2.12  tff(c_1218, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_1215])).
% 6.26/2.12  tff(c_1222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_1218])).
% 6.26/2.12  tff(c_1224, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1214])).
% 6.26/2.12  tff(c_1177, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1160])).
% 6.26/2.12  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_64, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_101, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_64])).
% 6.26/2.12  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_102, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 6.26/2.12  tff(c_1229, plain, (![A_404, B_405, C_406, D_407]: (v1_funct_2(k2_tmap_1(A_404, B_405, C_406, D_407), u1_struct_0(D_407), u1_struct_0(B_405)) | ~l1_struct_0(D_407) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_404), u1_struct_0(B_405)))) | ~v1_funct_2(C_406, u1_struct_0(A_404), u1_struct_0(B_405)) | ~v1_funct_1(C_406) | ~l1_struct_0(B_405) | ~l1_struct_0(A_404))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.26/2.12  tff(c_1233, plain, (![D_407]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_407), u1_struct_0(D_407), u1_struct_0('#skF_2')) | ~l1_struct_0(D_407) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_102, c_1229])).
% 6.26/2.12  tff(c_1241, plain, (![D_407]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_407), u1_struct_0(D_407), u1_struct_0('#skF_2')) | ~l1_struct_0(D_407))), inference(demodulation, [status(thm), theory('equality')], [c_1177, c_1187, c_66, c_101, c_1233])).
% 6.26/2.12  tff(c_30, plain, (![A_45, B_46, C_47, D_48]: (m1_subset_1(k2_tmap_1(A_45, B_46, C_47, D_48), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_48), u1_struct_0(B_46)))) | ~l1_struct_0(D_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_45), u1_struct_0(B_46)))) | ~v1_funct_2(C_47, u1_struct_0(A_45), u1_struct_0(B_46)) | ~v1_funct_1(C_47) | ~l1_struct_0(B_46) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.26/2.12  tff(c_1155, plain, (![D_396]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_396)) | ~l1_struct_0(D_396) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_102, c_1151])).
% 6.26/2.12  tff(c_1163, plain, (![D_396]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_396)) | ~l1_struct_0(D_396) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_101, c_1155])).
% 6.26/2.12  tff(c_1226, plain, (![D_396]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_396)) | ~l1_struct_0(D_396))), inference(demodulation, [status(thm), theory('equality')], [c_1177, c_1187, c_1163])).
% 6.26/2.12  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_84, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_96, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_84])).
% 6.26/2.12  tff(c_68, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_100, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_68])).
% 6.26/2.12  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_78, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_1820, plain, (![D_497, C_493, E_494, A_496, B_495]: (v1_funct_2(k3_tmap_1(A_496, B_495, C_493, D_497, E_494), u1_struct_0(D_497), u1_struct_0(B_495)) | ~m1_subset_1(E_494, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_493), u1_struct_0(B_495)))) | ~v1_funct_2(E_494, u1_struct_0(C_493), u1_struct_0(B_495)) | ~v1_funct_1(E_494) | ~m1_pre_topc(D_497, A_496) | ~m1_pre_topc(C_493, A_496) | ~l1_pre_topc(B_495) | ~v2_pre_topc(B_495) | v2_struct_0(B_495) | ~l1_pre_topc(A_496) | ~v2_pre_topc(A_496) | v2_struct_0(A_496))), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.26/2.12  tff(c_1826, plain, (![A_496, D_497]: (v1_funct_2(k3_tmap_1(A_496, '#skF_2', '#skF_4', D_497, '#skF_5'), u1_struct_0(D_497), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_497, A_496) | ~m1_pre_topc('#skF_4', A_496) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_496) | ~v2_pre_topc(A_496) | v2_struct_0(A_496))), inference(resolution, [status(thm)], [c_102, c_1820])).
% 6.26/2.12  tff(c_1836, plain, (![A_496, D_497]: (v1_funct_2(k3_tmap_1(A_496, '#skF_2', '#skF_4', D_497, '#skF_5'), u1_struct_0(D_497), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_497, A_496) | ~m1_pre_topc('#skF_4', A_496) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_496) | ~v2_pre_topc(A_496) | v2_struct_0(A_496))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_101, c_1826])).
% 6.26/2.12  tff(c_1842, plain, (![A_498, D_499]: (v1_funct_2(k3_tmap_1(A_498, '#skF_2', '#skF_4', D_499, '#skF_5'), u1_struct_0(D_499), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_499, A_498) | ~m1_pre_topc('#skF_4', A_498) | ~l1_pre_topc(A_498) | ~v2_pre_topc(A_498) | v2_struct_0(A_498))), inference(negUnitSimplification, [status(thm)], [c_80, c_1836])).
% 6.26/2.12  tff(c_1468, plain, (![C_454, D_458, B_456, E_455, A_457]: (v1_funct_1(k3_tmap_1(A_457, B_456, C_454, D_458, E_455)) | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_454), u1_struct_0(B_456)))) | ~v1_funct_2(E_455, u1_struct_0(C_454), u1_struct_0(B_456)) | ~v1_funct_1(E_455) | ~m1_pre_topc(D_458, A_457) | ~m1_pre_topc(C_454, A_457) | ~l1_pre_topc(B_456) | ~v2_pre_topc(B_456) | v2_struct_0(B_456) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.26/2.12  tff(c_1472, plain, (![A_457, D_458]: (v1_funct_1(k3_tmap_1(A_457, '#skF_2', '#skF_4', D_458, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_458, A_457) | ~m1_pre_topc('#skF_4', A_457) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(resolution, [status(thm)], [c_102, c_1468])).
% 6.26/2.12  tff(c_1478, plain, (![A_457, D_458]: (v1_funct_1(k3_tmap_1(A_457, '#skF_2', '#skF_4', D_458, '#skF_5')) | ~m1_pre_topc(D_458, A_457) | ~m1_pre_topc('#skF_4', A_457) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_66, c_101, c_1472])).
% 6.26/2.12  tff(c_1479, plain, (![A_457, D_458]: (v1_funct_1(k3_tmap_1(A_457, '#skF_2', '#skF_4', D_458, '#skF_5')) | ~m1_pre_topc(D_458, A_457) | ~m1_pre_topc('#skF_4', A_457) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(negUnitSimplification, [status(thm)], [c_80, c_1478])).
% 6.26/2.12  tff(c_1247, plain, (![F_412, C_410, B_411, D_414, A_413]: (r1_funct_2(A_413, B_411, C_410, D_414, F_412, F_412) | ~m1_subset_1(F_412, k1_zfmisc_1(k2_zfmisc_1(C_410, D_414))) | ~v1_funct_2(F_412, C_410, D_414) | ~m1_subset_1(F_412, k1_zfmisc_1(k2_zfmisc_1(A_413, B_411))) | ~v1_funct_2(F_412, A_413, B_411) | ~v1_funct_1(F_412) | v1_xboole_0(D_414) | v1_xboole_0(B_411))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.26/2.12  tff(c_1249, plain, (![A_413, B_411]: (r1_funct_2(A_413, B_411, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_7', '#skF_7') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_413, B_411))) | ~v1_funct_2('#skF_7', A_413, B_411) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_411))), inference(resolution, [status(thm)], [c_50, c_1247])).
% 6.26/2.12  tff(c_1256, plain, (![A_413, B_411]: (r1_funct_2(A_413, B_411, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_7', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_413, B_411))) | ~v1_funct_2('#skF_7', A_413, B_411) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_411))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1249])).
% 6.26/2.12  tff(c_1264, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1256])).
% 6.26/2.12  tff(c_22, plain, (![A_23]: (~v1_xboole_0(u1_struct_0(A_23)) | ~l1_struct_0(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.26/2.12  tff(c_1267, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1264, c_22])).
% 6.26/2.12  tff(c_1270, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_1267])).
% 6.26/2.12  tff(c_1272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1270])).
% 6.26/2.12  tff(c_1274, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1256])).
% 6.26/2.12  tff(c_46, plain, (r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_104, plain, (r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 6.26/2.12  tff(c_1356, plain, (![F_442, C_439, B_440, D_444, A_443, E_441]: (F_442=E_441 | ~r1_funct_2(A_443, B_440, C_439, D_444, E_441, F_442) | ~m1_subset_1(F_442, k1_zfmisc_1(k2_zfmisc_1(C_439, D_444))) | ~v1_funct_2(F_442, C_439, D_444) | ~v1_funct_1(F_442) | ~m1_subset_1(E_441, k1_zfmisc_1(k2_zfmisc_1(A_443, B_440))) | ~v1_funct_2(E_441, A_443, B_440) | ~v1_funct_1(E_441) | v1_xboole_0(D_444) | v1_xboole_0(B_440))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.26/2.12  tff(c_1364, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_104, c_1356])).
% 6.26/2.12  tff(c_1382, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_101, c_102, c_54, c_52, c_50, c_1364])).
% 6.26/2.12  tff(c_1383, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1274, c_1382])).
% 6.26/2.12  tff(c_294, plain, (![A_244, B_245, C_246, D_247]: (v1_funct_1(k2_tmap_1(A_244, B_245, C_246, D_247)) | ~l1_struct_0(D_247) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_244), u1_struct_0(B_245)))) | ~v1_funct_2(C_246, u1_struct_0(A_244), u1_struct_0(B_245)) | ~v1_funct_1(C_246) | ~l1_struct_0(B_245) | ~l1_struct_0(A_244))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.26/2.12  tff(c_296, plain, (![D_247]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_247)) | ~l1_struct_0(D_247) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_294])).
% 6.26/2.12  tff(c_303, plain, (![D_247]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_247)) | ~l1_struct_0(D_247) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_296])).
% 6.26/2.12  tff(c_310, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_303])).
% 6.26/2.12  tff(c_313, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_310])).
% 6.26/2.12  tff(c_317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_313])).
% 6.26/2.12  tff(c_318, plain, (![D_247]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_247)) | ~l1_struct_0(D_247))), inference(splitRight, [status(thm)], [c_303])).
% 6.26/2.12  tff(c_330, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_318])).
% 6.26/2.12  tff(c_333, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_330])).
% 6.26/2.12  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_333])).
% 6.26/2.12  tff(c_339, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_318])).
% 6.26/2.12  tff(c_587, plain, (![F_290, B_289, C_288, A_291, D_292]: (r1_funct_2(A_291, B_289, C_288, D_292, F_290, F_290) | ~m1_subset_1(F_290, k1_zfmisc_1(k2_zfmisc_1(C_288, D_292))) | ~v1_funct_2(F_290, C_288, D_292) | ~m1_subset_1(F_290, k1_zfmisc_1(k2_zfmisc_1(A_291, B_289))) | ~v1_funct_2(F_290, A_291, B_289) | ~v1_funct_1(F_290) | v1_xboole_0(D_292) | v1_xboole_0(B_289))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.26/2.12  tff(c_589, plain, (![A_291, B_289]: (r1_funct_2(A_291, B_289, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_7', '#skF_7') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_291, B_289))) | ~v1_funct_2('#skF_7', A_291, B_289) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_289))), inference(resolution, [status(thm)], [c_50, c_587])).
% 6.26/2.12  tff(c_596, plain, (![A_291, B_289]: (r1_funct_2(A_291, B_289, u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_7', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_291, B_289))) | ~v1_funct_2('#skF_7', A_291, B_289) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_289))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_589])).
% 6.26/2.12  tff(c_611, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_596])).
% 6.26/2.12  tff(c_614, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_611, c_22])).
% 6.26/2.12  tff(c_617, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_614])).
% 6.26/2.12  tff(c_619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_617])).
% 6.26/2.12  tff(c_621, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_596])).
% 6.26/2.12  tff(c_737, plain, (![E_323, A_325, B_322, D_326, C_321, F_324]: (F_324=E_323 | ~r1_funct_2(A_325, B_322, C_321, D_326, E_323, F_324) | ~m1_subset_1(F_324, k1_zfmisc_1(k2_zfmisc_1(C_321, D_326))) | ~v1_funct_2(F_324, C_321, D_326) | ~v1_funct_1(F_324) | ~m1_subset_1(E_323, k1_zfmisc_1(k2_zfmisc_1(A_325, B_322))) | ~v1_funct_2(E_323, A_325, B_322) | ~v1_funct_1(E_323) | v1_xboole_0(D_326) | v1_xboole_0(B_322))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.26/2.12  tff(c_745, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_104, c_737])).
% 6.26/2.12  tff(c_763, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_101, c_102, c_54, c_52, c_50, c_745])).
% 6.26/2.12  tff(c_764, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_621, c_763])).
% 6.26/2.12  tff(c_88, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_103, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_88])).
% 6.26/2.12  tff(c_258, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_103])).
% 6.26/2.12  tff(c_771, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_764, c_258])).
% 6.26/2.12  tff(c_300, plain, (![D_247]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_247)) | ~l1_struct_0(D_247) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_294])).
% 6.26/2.12  tff(c_309, plain, (![D_247]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_247)) | ~l1_struct_0(D_247) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_300])).
% 6.26/2.12  tff(c_320, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_309])).
% 6.26/2.12  tff(c_323, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_320])).
% 6.26/2.12  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_323])).
% 6.26/2.12  tff(c_329, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_309])).
% 6.26/2.12  tff(c_319, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_303])).
% 6.26/2.12  tff(c_513, plain, (![A_278, B_279, C_280, D_281]: (v1_funct_2(k2_tmap_1(A_278, B_279, C_280, D_281), u1_struct_0(D_281), u1_struct_0(B_279)) | ~l1_struct_0(D_281) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_278), u1_struct_0(B_279)))) | ~v1_funct_2(C_280, u1_struct_0(A_278), u1_struct_0(B_279)) | ~v1_funct_1(C_280) | ~l1_struct_0(B_279) | ~l1_struct_0(A_278))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.26/2.12  tff(c_519, plain, (![D_281]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_281), u1_struct_0(D_281), u1_struct_0('#skF_2')) | ~l1_struct_0(D_281) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_102, c_513])).
% 6.26/2.12  tff(c_535, plain, (![D_283]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_283), u1_struct_0(D_283), u1_struct_0('#skF_2')) | ~l1_struct_0(D_283))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_339, c_66, c_101, c_519])).
% 6.26/2.12  tff(c_433, plain, (![A_273, B_274, C_275, D_276]: (m1_subset_1(k2_tmap_1(A_273, B_274, C_275, D_276), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_276), u1_struct_0(B_274)))) | ~l1_struct_0(D_276) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_273), u1_struct_0(B_274)))) | ~v1_funct_2(C_275, u1_struct_0(A_273), u1_struct_0(B_274)) | ~v1_funct_1(C_275) | ~l1_struct_0(B_274) | ~l1_struct_0(A_273))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.26/2.12  tff(c_298, plain, (![D_247]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_247)) | ~l1_struct_0(D_247) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_102, c_294])).
% 6.26/2.12  tff(c_306, plain, (![D_247]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_247)) | ~l1_struct_0(D_247) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_101, c_298])).
% 6.26/2.12  tff(c_369, plain, (![D_247]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_247)) | ~l1_struct_0(D_247))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_339, c_306])).
% 6.26/2.12  tff(c_94, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_291])).
% 6.26/2.12  tff(c_99, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_94])).
% 6.26/2.12  tff(c_293, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_258, c_99])).
% 6.26/2.12  tff(c_340, plain, (![D_248, C_249, A_250, B_251]: (D_248=C_249 | ~r2_funct_2(A_250, B_251, C_249, D_248) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))) | ~v1_funct_2(D_248, A_250, B_251) | ~v1_funct_1(D_248) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))) | ~v1_funct_2(C_249, A_250, B_251) | ~v1_funct_1(C_249))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.26/2.12  tff(c_342, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_293, c_340])).
% 6.26/2.12  tff(c_351, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_342])).
% 6.26/2.12  tff(c_371, plain, (~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_351])).
% 6.26/2.12  tff(c_374, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_369, c_371])).
% 6.26/2.12  tff(c_378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_329, c_374])).
% 6.26/2.12  tff(c_379, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_351])).
% 6.26/2.12  tff(c_381, plain, (~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_379])).
% 6.26/2.12  tff(c_440, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_433, c_381])).
% 6.26/2.12  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_319, c_339, c_66, c_101, c_102, c_329, c_440])).
% 6.26/2.12  tff(c_462, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_379])).
% 6.26/2.12  tff(c_493, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_462])).
% 6.26/2.12  tff(c_538, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_535, c_493])).
% 6.26/2.12  tff(c_542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_329, c_538])).
% 6.26/2.12  tff(c_543, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_462])).
% 6.26/2.12  tff(c_217, plain, (![A_232, B_233, C_234, D_235]: (k2_partfun1(A_232, B_233, C_234, D_235)=k7_relat_1(C_234, D_235) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~v1_funct_1(C_234))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.26/2.12  tff(c_221, plain, (![D_235]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_235)=k7_relat_1('#skF_5', D_235) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_102, c_217])).
% 6.26/2.12  tff(c_229, plain, (![D_235]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_235)=k7_relat_1('#skF_5', D_235))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_221])).
% 6.26/2.12  tff(c_864, plain, (![A_344, B_345, C_346, D_347]: (k2_partfun1(u1_struct_0(A_344), u1_struct_0(B_345), C_346, u1_struct_0(D_347))=k2_tmap_1(A_344, B_345, C_346, D_347) | ~m1_pre_topc(D_347, A_344) | ~m1_subset_1(C_346, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_344), u1_struct_0(B_345)))) | ~v1_funct_2(C_346, u1_struct_0(A_344), u1_struct_0(B_345)) | ~v1_funct_1(C_346) | ~l1_pre_topc(B_345) | ~v2_pre_topc(B_345) | v2_struct_0(B_345) | ~l1_pre_topc(A_344) | ~v2_pre_topc(A_344) | v2_struct_0(A_344))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.26/2.12  tff(c_868, plain, (![D_347]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_347))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_347) | ~m1_pre_topc(D_347, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_102, c_864])).
% 6.26/2.12  tff(c_874, plain, (![D_347]: (k7_relat_1('#skF_5', u1_struct_0(D_347))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_347) | ~m1_pre_topc(D_347, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_97, c_78, c_76, c_66, c_101, c_229, c_868])).
% 6.26/2.12  tff(c_880, plain, (![D_348]: (k7_relat_1('#skF_5', u1_struct_0(D_348))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_348) | ~m1_pre_topc(D_348, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_70, c_80, c_874])).
% 6.26/2.12  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.26/2.12  tff(c_125, plain, (![B_218, A_219]: (v1_relat_1(B_218) | ~m1_subset_1(B_218, k1_zfmisc_1(A_219)) | ~v1_relat_1(A_219))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.26/2.12  tff(c_128, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_102, c_125])).
% 6.26/2.12  tff(c_134, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_128])).
% 6.26/2.12  tff(c_144, plain, (![C_220, A_221, B_222]: (v4_relat_1(C_220, A_221) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.26/2.12  tff(c_155, plain, (v4_relat_1('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_102, c_144])).
% 6.26/2.12  tff(c_170, plain, (![B_226, A_227]: (k7_relat_1(B_226, A_227)=B_226 | ~v4_relat_1(B_226, A_227) | ~v1_relat_1(B_226))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.26/2.12  tff(c_173, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_155, c_170])).
% 6.26/2.12  tff(c_182, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_173])).
% 6.26/2.12  tff(c_886, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_880, c_182])).
% 6.26/2.12  tff(c_895, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_886])).
% 6.26/2.12  tff(c_1065, plain, (![C_386, D_383, A_385, E_387, B_384]: (r2_funct_2(u1_struct_0(C_386), u1_struct_0(B_384), k3_tmap_1(A_385, B_384, D_383, C_386, k2_tmap_1(A_385, B_384, E_387, D_383)), k2_tmap_1(A_385, B_384, E_387, C_386)) | ~m1_pre_topc(C_386, D_383) | ~m1_subset_1(E_387, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_385), u1_struct_0(B_384)))) | ~v1_funct_2(E_387, u1_struct_0(A_385), u1_struct_0(B_384)) | ~v1_funct_1(E_387) | ~m1_pre_topc(D_383, A_385) | v2_struct_0(D_383) | ~m1_pre_topc(C_386, A_385) | v2_struct_0(C_386) | ~l1_pre_topc(B_384) | ~v2_pre_topc(B_384) | v2_struct_0(B_384) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385))), inference(cnfTransformation, [status(thm)], [f_222])).
% 6.26/2.12  tff(c_1070, plain, (![C_386]: (r2_funct_2(u1_struct_0(C_386), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_386, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_386)) | ~m1_pre_topc(C_386, '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_386, '#skF_4') | v2_struct_0(C_386) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_895, c_1065])).
% 6.26/2.12  tff(c_1082, plain, (![C_386]: (r2_funct_2(u1_struct_0(C_386), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_386, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_386)) | ~m1_pre_topc(C_386, '#skF_4') | v2_struct_0(C_386) | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_97, c_78, c_76, c_100, c_66, c_101, c_102, c_1070])).
% 6.26/2.12  tff(c_1093, plain, (![C_388]: (r2_funct_2(u1_struct_0(C_388), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_388, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_388)) | ~m1_pre_topc(C_388, '#skF_4') | v2_struct_0(C_388))), inference(negUnitSimplification, [status(thm)], [c_70, c_80, c_1082])).
% 6.26/2.12  tff(c_1101, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_543, c_1093])).
% 6.26/2.12  tff(c_1107, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1101])).
% 6.26/2.12  tff(c_1109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_771, c_1107])).
% 6.26/2.12  tff(c_1111, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_103])).
% 6.26/2.12  tff(c_1188, plain, (![D_397, C_398, A_399, B_400]: (D_397=C_398 | ~r2_funct_2(A_399, B_400, C_398, D_397) | ~m1_subset_1(D_397, k1_zfmisc_1(k2_zfmisc_1(A_399, B_400))) | ~v1_funct_2(D_397, A_399, B_400) | ~v1_funct_1(D_397) | ~m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1(A_399, B_400))) | ~v1_funct_2(C_398, A_399, B_400) | ~v1_funct_1(C_398))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.26/2.12  tff(c_1190, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'))), inference(resolution, [status(thm)], [c_1111, c_1188])).
% 6.26/2.12  tff(c_1199, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_1190])).
% 6.26/2.12  tff(c_1486, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_1383, c_1383, c_1383, c_1199])).
% 6.26/2.12  tff(c_1487, plain, (~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1486])).
% 6.26/2.12  tff(c_1491, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1479, c_1487])).
% 6.26/2.12  tff(c_1494, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_97, c_100, c_98, c_1491])).
% 6.26/2.12  tff(c_1496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1494])).
% 6.26/2.12  tff(c_1498, plain, (v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_1486])).
% 6.26/2.12  tff(c_1610, plain, (![B_484, C_482, D_486, E_483, A_485]: (m1_subset_1(k3_tmap_1(A_485, B_484, C_482, D_486, E_483), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_486), u1_struct_0(B_484)))) | ~m1_subset_1(E_483, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_482), u1_struct_0(B_484)))) | ~v1_funct_2(E_483, u1_struct_0(C_482), u1_struct_0(B_484)) | ~v1_funct_1(E_483) | ~m1_pre_topc(D_486, A_485) | ~m1_pre_topc(C_482, A_485) | ~l1_pre_topc(B_484) | ~v2_pre_topc(B_484) | v2_struct_0(B_484) | ~l1_pre_topc(A_485) | ~v2_pre_topc(A_485) | v2_struct_0(A_485))), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.26/2.12  tff(c_1497, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_1486])).
% 6.26/2.12  tff(c_1499, plain, (~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1497])).
% 6.26/2.12  tff(c_1619, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1610, c_1499])).
% 6.26/2.12  tff(c_1652, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_97, c_78, c_76, c_100, c_98, c_66, c_101, c_102, c_1619])).
% 6.26/2.12  tff(c_1654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_80, c_1652])).
% 6.26/2.12  tff(c_1656, plain, (m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_1497])).
% 6.26/2.12  tff(c_40, plain, (![D_52, C_51, B_50, A_49, E_53]: (v1_funct_1(k3_tmap_1(A_49, B_50, C_51, D_52, E_53)) | ~m1_subset_1(E_53, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_51), u1_struct_0(B_50)))) | ~v1_funct_2(E_53, u1_struct_0(C_51), u1_struct_0(B_50)) | ~v1_funct_1(E_53) | ~m1_pre_topc(D_52, A_49) | ~m1_pre_topc(C_51, A_49) | ~l1_pre_topc(B_50) | ~v2_pre_topc(B_50) | v2_struct_0(B_50) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.26/2.12  tff(c_1658, plain, (![A_49, D_52]: (v1_funct_1(k3_tmap_1(A_49, '#skF_2', '#skF_3', D_52, k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')) | ~m1_pre_topc(D_52, A_49) | ~m1_pre_topc('#skF_3', A_49) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_1656, c_40])).
% 6.26/2.12  tff(c_1686, plain, (![A_49, D_52]: (v1_funct_1(k3_tmap_1(A_49, '#skF_2', '#skF_3', D_52, k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_52, A_49) | ~m1_pre_topc('#skF_3', A_49) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1498, c_1658])).
% 6.26/2.12  tff(c_1687, plain, (![A_49, D_52]: (v1_funct_1(k3_tmap_1(A_49, '#skF_2', '#skF_3', D_52, k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_52, A_49) | ~m1_pre_topc('#skF_3', A_49) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(negUnitSimplification, [status(thm)], [c_80, c_1686])).
% 6.26/2.12  tff(c_1718, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1687])).
% 6.26/2.12  tff(c_1845, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1842, c_1718])).
% 6.26/2.12  tff(c_1848, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_97, c_100, c_98, c_1845])).
% 6.26/2.12  tff(c_1850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1848])).
% 6.26/2.12  tff(c_1852, plain, (v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1687])).
% 6.26/2.12  tff(c_1655, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_1497])).
% 6.26/2.12  tff(c_1865, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1852, c_1655])).
% 6.26/2.12  tff(c_1898, plain, (![A_502, B_503, C_504, D_505]: (k2_partfun1(u1_struct_0(A_502), u1_struct_0(B_503), C_504, u1_struct_0(D_505))=k2_tmap_1(A_502, B_503, C_504, D_505) | ~m1_pre_topc(D_505, A_502) | ~m1_subset_1(C_504, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_502), u1_struct_0(B_503)))) | ~v1_funct_2(C_504, u1_struct_0(A_502), u1_struct_0(B_503)) | ~v1_funct_1(C_504) | ~l1_pre_topc(B_503) | ~v2_pre_topc(B_503) | v2_struct_0(B_503) | ~l1_pre_topc(A_502) | ~v2_pre_topc(A_502) | v2_struct_0(A_502))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.26/2.12  tff(c_1902, plain, (![D_505]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_505))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_505) | ~m1_pre_topc(D_505, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_102, c_1898])).
% 6.26/2.12  tff(c_1908, plain, (![D_505]: (k7_relat_1('#skF_5', u1_struct_0(D_505))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_505) | ~m1_pre_topc(D_505, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_97, c_78, c_76, c_66, c_101, c_229, c_1902])).
% 6.26/2.12  tff(c_1914, plain, (![D_506]: (k7_relat_1('#skF_5', u1_struct_0(D_506))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_506) | ~m1_pre_topc(D_506, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_70, c_80, c_1908])).
% 6.26/2.12  tff(c_1920, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1914, c_182])).
% 6.26/2.12  tff(c_1929, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1920])).
% 6.26/2.12  tff(c_2123, plain, (![E_539, B_536, D_535, A_537, C_538]: (r2_funct_2(u1_struct_0(C_538), u1_struct_0(B_536), k3_tmap_1(A_537, B_536, D_535, C_538, k2_tmap_1(A_537, B_536, E_539, D_535)), k2_tmap_1(A_537, B_536, E_539, C_538)) | ~m1_pre_topc(C_538, D_535) | ~m1_subset_1(E_539, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_537), u1_struct_0(B_536)))) | ~v1_funct_2(E_539, u1_struct_0(A_537), u1_struct_0(B_536)) | ~v1_funct_1(E_539) | ~m1_pre_topc(D_535, A_537) | v2_struct_0(D_535) | ~m1_pre_topc(C_538, A_537) | v2_struct_0(C_538) | ~l1_pre_topc(B_536) | ~v2_pre_topc(B_536) | v2_struct_0(B_536) | ~l1_pre_topc(A_537) | ~v2_pre_topc(A_537) | v2_struct_0(A_537))), inference(cnfTransformation, [status(thm)], [f_222])).
% 6.26/2.12  tff(c_2128, plain, (![C_538]: (r2_funct_2(u1_struct_0(C_538), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_538, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_538)) | ~m1_pre_topc(C_538, '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_538, '#skF_4') | v2_struct_0(C_538) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1929, c_2123])).
% 6.26/2.12  tff(c_2134, plain, (![C_538]: (r2_funct_2(u1_struct_0(C_538), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_538, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_538)) | ~m1_pre_topc(C_538, '#skF_4') | v2_struct_0(C_538) | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_97, c_78, c_76, c_100, c_66, c_101, c_102, c_2128])).
% 6.26/2.12  tff(c_2147, plain, (![C_544]: (r2_funct_2(u1_struct_0(C_544), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_544, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_544)) | ~m1_pre_topc(C_544, '#skF_4') | v2_struct_0(C_544))), inference(negUnitSimplification, [status(thm)], [c_70, c_80, c_2134])).
% 6.26/2.12  tff(c_2155, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1865, c_2147])).
% 6.26/2.12  tff(c_2161, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_2155])).
% 6.26/2.12  tff(c_2162, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_74, c_2161])).
% 6.26/2.12  tff(c_16, plain, (![D_18, C_17, A_15, B_16]: (D_18=C_17 | ~r2_funct_2(A_15, B_16, C_17, D_18) | ~m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_funct_2(D_18, A_15, B_16) | ~v1_funct_1(D_18) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))) | ~v1_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.26/2.12  tff(c_2164, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_2162, c_16])).
% 6.26/2.12  tff(c_2167, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_2164])).
% 6.26/2.12  tff(c_2185, plain, (~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2167])).
% 6.26/2.12  tff(c_2188, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1226, c_2185])).
% 6.26/2.12  tff(c_2192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1224, c_2188])).
% 6.26/2.12  tff(c_2193, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_2167])).
% 6.26/2.12  tff(c_2222, plain, (~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_2193])).
% 6.26/2.12  tff(c_2240, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_2222])).
% 6.26/2.12  tff(c_2244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1177, c_1187, c_66, c_101, c_102, c_1224, c_2240])).
% 6.26/2.12  tff(c_2245, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_2193])).
% 6.26/2.12  tff(c_2384, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2245])).
% 6.26/2.12  tff(c_2387, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1241, c_2384])).
% 6.26/2.12  tff(c_2391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1224, c_2387])).
% 6.26/2.12  tff(c_2392, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_2245])).
% 6.26/2.12  tff(c_1110, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_103])).
% 6.26/2.12  tff(c_2412, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_1110])).
% 6.26/2.12  tff(c_2422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_257, c_2412])).
% 6.26/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.26/2.12  
% 6.26/2.12  Inference rules
% 6.26/2.12  ----------------------
% 6.26/2.12  #Ref     : 0
% 6.26/2.12  #Sup     : 433
% 6.26/2.12  #Fact    : 0
% 6.26/2.12  #Define  : 0
% 6.26/2.12  #Split   : 27
% 6.26/2.12  #Chain   : 0
% 6.26/2.12  #Close   : 0
% 6.26/2.12  
% 6.26/2.12  Ordering : KBO
% 6.26/2.12  
% 6.26/2.12  Simplification rules
% 6.26/2.12  ----------------------
% 6.26/2.12  #Subsume      : 35
% 6.26/2.12  #Demod        : 960
% 6.26/2.12  #Tautology    : 188
% 6.26/2.12  #SimpNegUnit  : 84
% 6.26/2.12  #BackRed      : 55
% 6.26/2.12  
% 6.26/2.12  #Partial instantiations: 0
% 6.26/2.12  #Strategies tried      : 1
% 6.26/2.12  
% 6.26/2.12  Timing (in seconds)
% 6.26/2.12  ----------------------
% 6.26/2.14  Preprocessing        : 0.42
% 6.26/2.14  Parsing              : 0.21
% 6.26/2.14  CNF conversion       : 0.05
% 6.26/2.14  Main loop            : 0.86
% 6.26/2.14  Inferencing          : 0.30
% 6.26/2.14  Reduction            : 0.30
% 6.26/2.14  Demodulation         : 0.23
% 6.26/2.14  BG Simplification    : 0.04
% 6.26/2.14  Subsumption          : 0.16
% 6.26/2.14  Abstraction          : 0.04
% 6.26/2.14  MUC search           : 0.00
% 6.26/2.14  Cooper               : 0.00
% 6.26/2.14  Total                : 1.40
% 6.26/2.14  Index Insertion      : 0.00
% 6.26/2.14  Index Deletion       : 0.00
% 6.26/2.14  Index Matching       : 0.00
% 6.26/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
